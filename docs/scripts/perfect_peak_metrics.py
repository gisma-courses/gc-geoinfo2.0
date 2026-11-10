"""
Perfect Peak Metrics

PyQGIS Processing script for QGIS 3.44+.

Input:  a projected DEM and either summit points or a summit mask.
        Summit points are snapped to the highest cell within a search radius.
Output: summit points (moved to the analysed cell) with raster-based
        dominance, a saddle interval, a prominence interval, the distance to
        the DGM edge, and an explicit validity status.

The algorithm calculates the article E interval and, separately, the actual
branch implemented in the historic perfectPeak R code. Both remain visible so
that the 100-km rule can be discussed instead of being silently inherited.
"""

from bisect import bisect_right
from collections import deque
from math import floor, hypot, log2

from qgis.core import (
    QgsCoordinateTransform,
    QgsFeature,
    QgsFeatureSink,
    QgsField,
    QgsFields,
    QgsGeometry,
    QgsPointXY,
    QgsProcessing,
    QgsProcessingAlgorithm,
    QgsProcessingException,
    QgsProcessingParameterDistance,
    QgsProcessingParameterEnum,
    QgsProcessingParameterFeatureSink,
    QgsProcessingParameterFeatureSource,
    QgsProcessingParameterNumber,
    QgsProcessingParameterRasterLayer,
    QgsWkbTypes,
)
from qgis.PyQt.QtCore import QVariant


# ---------------------------------------------------------------------------
# Raster logic without QGIS dependencies. The functions operate on a flat list
# of cell values (row-major, None = NoData) so that they can be tested outside
# QGIS against the teaching DEM.
# ---------------------------------------------------------------------------

OFFSETS_4 = ((-1, 0), (1, 0), (0, -1), (0, 1))
OFFSETS_8 = (
    (-1, 0), (-1, 1), (0, 1), (1, 1),
    (1, 0), (1, -1), (0, -1), (-1, -1),
)


def snap_to_local_maximum(values, rows, cols, row, col, radius):
    """Move a clicked point to the highest valid cell within `radius` cells.

    A digitised summit rarely hits the highest raster cell exactly. Without
    snapping, a neighbouring higher cell 10 m away would be reported as
    dominance and the prominence would collapse to zero.
    """
    best = (row, col)
    best_value = values[row * cols + col]
    for r in range(max(0, row - radius), min(rows, row + radius + 1)):
        for c in range(max(0, col - radius), min(cols, col + radius + 1)):
            value = values[r * cols + c]
            if value is not None and (best_value is None or value > best_value):
                best, best_value = (r, c), value
    return best[0], best[1]


def is_local_maximum(values, rows, cols, offsets, row, col):
    """True if no neighbouring cell is strictly higher."""
    height = values[row * cols + col]
    for dr, dc in offsets:
        r, c = row + dr, col + dc
        if 0 <= r < rows and 0 <= c < cols:
            value = values[r * cols + c]
            if value is not None and value > height:
                return False
    return True


def distance_to_edge(rows, cols, row, col, xres, yres):
    """Distance from the cell centre to the outer DGM boundary (m)."""
    return min(
        (col + 0.5) * xres,
        (cols - col - 0.5) * xres,
        (row + 0.5) * yres,
        (rows - row - 0.5) * yres,
    )


def nearest_higher_distance(values, cols, row, col, height, tolerance, xres, yres):
    """Distance between raster-cell centres, matching GDAL proximity."""
    best = None
    for index, value in enumerate(values):
        if value is None or value <= height + tolerance:
            continue
        other_row, other_col = divmod(index, cols)
        distance = hypot((other_col - col) * xres, (other_row - row) * yres)
        if best is None or distance < best:
            best = distance
    return best


def connected_to_higher(values, rows, cols, offsets, start_index,
                        summit_height, threshold, tolerance, stop_early=True):
    """Flood the component of cells >= threshold that contains the summit.

    Returns (reaches_higher_terrain, touches_dgm_edge). With stop_early the
    search ends at the first higher cell; the edge flag is then incomplete.
    """
    if values[start_index] is None or values[start_index] < threshold:
        return False, False
    seen = bytearray(rows * cols)
    queue = deque([start_index])
    seen[start_index] = 1
    touches_edge = False
    reaches_higher = False
    while queue:
        index = queue.popleft()
        row, col = divmod(index, cols)
        if row == 0 or row == rows - 1 or col == 0 or col == cols - 1:
            touches_edge = True
        if values[index] > summit_height + tolerance:
            reaches_higher = True
            if stop_early:
                return True, touches_edge
        for dr, dc in offsets:
            next_row, next_col = row + dr, col + dc
            if next_row < 0 or next_row >= rows or next_col < 0 or next_col >= cols:
                continue
            next_index = next_row * cols + next_col
            if (
                not seen[next_index]
                and values[next_index] is not None
                and values[next_index] >= threshold
            ):
                seen[next_index] = 1
                queue.append(next_index)
    return reaches_higher, touches_edge


def saddle_interval(values, rows, cols, offsets, levels, start_index,
                    summit_height, tolerance):
    """Find the highest DGM level that still connects to higher terrain.

    Returns (saddle_low, saddle_high, island_touches_edge, error). The island is
    the summit's own, still separated area just above the saddle. If it touches
    the DGM edge, a higher connection outside the data cannot be ruled out.
    """
    maximum_level_index = bisect_right(levels, summit_height) - 1
    if maximum_level_index < 0:
        return None, None, None, "invalid_summit_height"
    connected, _ = connected_to_higher(
        values, rows, cols, offsets, start_index, summit_height, levels[0], tolerance
    )
    if not connected:
        return None, None, None, "disconnected_in_raster"

    low, high, best = 0, maximum_level_index, 0
    while low <= high:
        middle = (low + high) // 2
        connected, _ = connected_to_higher(
            values, rows, cols, offsets, start_index, summit_height,
            levels[middle], tolerance,
        )
        if connected:
            best = middle
            low = middle + 1
        else:
            high = middle - 1

    saddle_low = levels[best]
    saddle_high = (
        levels[best + 1] if best + 1 <= maximum_level_index else summit_height
    )
    _, island_edge = connected_to_higher(
        values, rows, cols, offsets, start_index, summit_height,
        saddle_high, tolerance, stop_early=False,
    )
    return saddle_low, saddle_high, island_edge, None


def e_value(height, dominance, prominence, historic_code=False):
    """Calculate E from the article or the historic code branch.

    Article/formula graphic: use the dominance term for d < 100 km.
    Historic calculateIndependence.R executes the opposite branch.
    Smaller E means a more independent summit (Mount Everest: E = 0).
    """
    if height <= 0 or dominance <= 0 or prominence <= 0:
        return None
    use_dominance = dominance > 100000.0 if historic_code else dominance < 100000.0
    terms = [log2(height / 8848.0), log2(prominence / height)]
    if use_dominance:
        terms.insert(1, log2(dominance / 100000.0))
    return -sum(terms) / 3.0



class PerfectPeakMetrics(QgsProcessingAlgorithm):
    DEM = "DEM"
    SUMMITS = "SUMMITS"
    PEAK_MASK = "PEAK_MASK"
    HIGHER_TOLERANCE = "HIGHER_TOLERANCE"
    SNAP_RADIUS = "SNAP_RADIUS"
    CONNECTIVITY = "CONNECTIVITY"
    OUTPUT = "OUTPUT"

    def name(self):
        return "perfect_peak_metrics"

    def displayName(self):
        return "Perfect Peak: Dominanz und Prominenzintervall"

    def group(self):
        return "Perfect Peak"

    def groupId(self):
        return "perfect_peak"

    def shortHelpString(self):
        return """
        Berechnet für vorgegebene Gipfelpunkte oder alle positiven Bereiche einer
        Gipfelmaske die rasterbasierte Dominanz sowie ein Scharten- und
        Prominenzintervall. Das DGM und die Eingaben müssen in einem projizierten
        KBS mit Meter-Einheiten vorliegen.

        Gipfelpunkte werden auf die höchste Zelle im Fangradius gesetzt;
        snap_m gibt die Verschiebung an.

        Status:
        ok – Dominanz und Scharte sind innerhalb des DGM bestimmt.
        edge_relevant – die Fläche des Gipfels oberhalb der Scharte berührt
        den DGM-Rand oder der DGM-Rand liegt näher als das gefundene höhere
        Gelände; das Ergebnis ist nur ausschnittsbezogen.
        no_higher_terrain_in_dem – im DGM gibt es kein höheres Gelände.
        not_local_maximum – auch nach dem Fangen ist der Punkt kein lokales
        Maximum; Fangradius erhöhen oder Punkt prüfen.
        outside_dem / nodata_cell – Punkt liegt außerhalb gültiger Daten.
        """

    def initAlgorithm(self, config=None):
        self.addParameter(
            QgsProcessingParameterRasterLayer(
                self.DEM, "DGM (ein Band, projiziert in Metern)"
            )
        )
        self.addParameter(
            QgsProcessingParameterFeatureSource(
                self.SUMMITS,
                "Gipfelpunkte (optional; hat Vorrang vor der Maske)",
                [QgsProcessing.TypeVectorPoint],
                optional=True,
            )
        )
        self.addParameter(
            QgsProcessingParameterRasterLayer(
                self.PEAK_MASK,
                "Gipfelmaske (optional; Werte > 0 sind Kandidaten)",
                optional=True,
            )
        )
        self.addParameter(
            QgsProcessingParameterDistance(
                self.HIGHER_TOLERANCE,
                "Mindesthöhenunterschied für 'höheres Gelände' (m)",
                defaultValue=0.0,
                parentParameterName=self.DEM,
            )
        )
        self.addParameter(
            QgsProcessingParameterNumber(
                self.SNAP_RADIUS,
                "Fangradius für Gipfelpunkte (Rasterzellen; 0 = aus)",
                type=QgsProcessingParameterNumber.Integer,
                minValue=0,
                maxValue=25,
                defaultValue=3,
            )
        )
        self.addParameter(
            QgsProcessingParameterEnum(
                self.CONNECTIVITY,
                "Raster-Nachbarschaft",
                options=["4er-Nachbarschaft", "8er-Nachbarschaft"],
                defaultValue=1,
            )
        )
        self.addParameter(
            QgsProcessingParameterFeatureSink(
                self.OUTPUT, "Gipfelwerte", QgsProcessing.TypeVectorPoint
            )
        )

    def processAlgorithm(self, parameters, context, feedback):
        dem = self.parameterAsRasterLayer(parameters, self.DEM, context)
        source = self.parameterAsSource(parameters, self.SUMMITS, context)
        peak_mask = self.parameterAsRasterLayer(parameters, self.PEAK_MASK, context)
        if dem is None:
            raise QgsProcessingException("Das DGM fehlt.")
        if source is None and peak_mask is None:
            raise QgsProcessingException("Gipfelpunkte oder Gipfelmaske fehlen.")

        provider = dem.dataProvider()
        extent = provider.extent()
        cols, rows = provider.xSize(), provider.ySize()
        if cols < 1 or rows < 1:
            raise QgsProcessingException("Das DGM enthält keine Rasterzellen.")

        xres = extent.width() / cols
        yres = extent.height() / rows
        if xres <= 0 or yres <= 0:
            raise QgsProcessingException("Die Rasterauflösung des DGM ist ungültig.")

        higher_tolerance = self.parameterAsDouble(
            parameters, self.HIGHER_TOLERANCE, context
        )
        connectivity = self.parameterAsEnum(parameters, self.CONNECTIVITY, context)
        snap_radius = self.parameterAsInt(parameters, self.SNAP_RADIUS, context)

        # Read once: the teaching DEM is small, and this avoids temporary files.
        block = provider.block(1, extent, cols, rows)
        cell_count = cols * rows
        values = [None] * cell_count
        valid_values = []
        for row in range(rows):
            for col in range(cols):
                index = row * cols + col
                if not block.isNoData(row, col):
                    value = float(block.value(row, col))
                    values[index] = value
                    valid_values.append(value)

        if not valid_values:
            raise QgsProcessingException("Das DGM enthält nur NoData-Zellen.")
        levels = sorted(set(valid_values))

        neighbour_offsets = OFFSETS_4 if connectivity == 0 else OFFSETS_8

        out_fields = QgsFields(source.fields()) if source is not None else QgsFields()
        for name, field_type in (
            ("pp_id", QVariant.String),
            ("snap_m", QVariant.Double),
            ("peak_h_m", QVariant.Double),
            ("rand_m", QVariant.Double),
            ("dominanz_m", QVariant.Double),
            ("scharte_lo", QVariant.Double),
            ("scharte_hi", QVariant.Double),
            ("prom_lo_m", QVariant.Double),
            ("prom_hi_m", QVariant.Double),
            ("e_art_lo", QVariant.Double),
            ("e_art_hi", QVariant.Double),
            ("e_code_lo", QVariant.Double),
            ("e_code_hi", QVariant.Double),
            ("e_note", QVariant.String),
            ("pp_status", QVariant.String),
        ):
            field_length = 96 if name == "e_note" else 32
            out_fields.append(QgsField(name, field_type, "", field_length, 3))

        sink, destination = self.parameterAsSink(
            parameters,
            self.OUTPUT,
            context,
            out_fields,
            source.wkbType() if source is not None else QgsWkbTypes.Point,
            source.sourceCrs() if source is not None else dem.crs(),
        )
        if sink is None:
            raise QgsProcessingException("Ausgabelayer konnte nicht erstellt werden.")

        transform = (
            QgsCoordinateTransform(source.sourceCrs(), dem.crs(), context.transformContext())
            if source is not None
            else None
        )
        reverse_transform = (
            QgsCoordinateTransform(dem.crs(), source.sourceCrs(), context.transformContext())
            if source is not None
            else None
        )
        features = list(source.getFeatures()) if source is not None else []

        def cell_for_point(point):
            col = int(floor((point.x() - extent.xMinimum()) / xres))
            row = int(floor((extent.yMaximum() - point.y()) / yres))
            if row < 0 or row >= rows or col < 0 or col >= cols:
                return None
            return row, col, row * cols + col

        def features_from_mask(mask_layer):
            """Create one summit point per connected positive mask component."""
            mask_provider = mask_layer.dataProvider()
            if (
                mask_layer.crs() != dem.crs()
                or mask_provider.xSize() != cols
                or mask_provider.ySize() != rows
                or mask_provider.extent() != extent
            ):
                raise QgsProcessingException(
                    "Die Gipfelmaske muss dasselbe KBS, dieselbe Ausdehnung und "
                    "dasselbe Rastergitter wie das DGM besitzen."
                )

            mask_block = mask_provider.block(1, extent, cols, rows)
            candidates = bytearray(cell_count)
            for row in range(rows):
                for col in range(cols):
                    index = row * cols + col
                    if (
                        values[index] is not None
                        and not mask_block.isNoData(row, col)
                        and float(mask_block.value(row, col)) > 0
                    ):
                        candidates[index] = 1

            seen = bytearray(cell_count)
            output = []
            for start_index in range(cell_count):
                if not candidates[start_index] or seen[start_index]:
                    continue
                seen[start_index] = 1
                queue = deque([start_index])
                best_index = start_index
                while queue:
                    index = queue.popleft()
                    if values[index] > values[best_index]:
                        best_index = index
                    row, col = divmod(index, cols)
                    for dr, dc in neighbour_offsets:
                        next_row, next_col = row + dr, col + dc
                        if next_row < 0 or next_row >= rows or next_col < 0 or next_col >= cols:
                            continue
                        next_index = next_row * cols + next_col
                        if candidates[next_index] and not seen[next_index]:
                            seen[next_index] = 1
                            queue.append(next_index)

                row, col = divmod(best_index, cols)
                x = extent.xMinimum() + (col + 0.5) * xres
                y = extent.yMaximum() - (row + 0.5) * yres
                feature = QgsFeature()
                feature.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(x, y)))
                output.append(feature)
            return output

        if source is None:
            features = features_from_mask(peak_mask)
            feedback.pushInfo(
                "{0} Gipfelkandidaten aus der Maske erzeugt.".format(len(features))
            )
        total = max(1, len(features))

        for feature_number, feature in enumerate(features):
            if feedback.isCanceled():
                break

            result = QgsFeature(out_fields)
            attributes = feature.attributes()
            snap_distance = peak_height = edge_distance = dominance = None
            saddle_low = saddle_high = None
            prominence_low = prominence_high = None
            e_article_low = e_article_high = None
            e_code_low = e_code_high = None
            e_note = "not_calculated"
            status = "invalid_geometry"
            geometry = feature.geometry()

            if feature.hasGeometry() and not geometry.isEmpty():
                point = geometry.asPoint()
                if transform is not None:
                    point = transform.transform(point)
                cell = cell_for_point(point)
                if cell is None:
                    status = "outside_dem"
                elif values[cell[2]] is None:
                    status = "nodata_cell"
                else:
                    row, col, _ = cell
                    if source is not None and snap_radius > 0:
                        row, col = snap_to_local_maximum(
                            values, rows, cols, row, col, snap_radius
                        )
                    index = row * cols + col
                    centre_x = extent.xMinimum() + (col + 0.5) * xres
                    centre_y = extent.yMaximum() - (row + 0.5) * yres
                    snap_distance = hypot(centre_x - point.x(), centre_y - point.y())
                    # Output geometry = analysed raster cell (in DGM CRS).
                    geometry = QgsGeometry.fromPointXY(QgsPointXY(centre_x, centre_y))
                    if reverse_transform is not None:
                        geometry.transform(reverse_transform)
                    peak_height = values[index]
                    edge_distance = distance_to_edge(rows, cols, row, col, xres, yres)

                    if not is_local_maximum(values, rows, cols, neighbour_offsets, row, col):
                        status = "not_local_maximum"
                    else:
                        dominance = nearest_higher_distance(
                            values, cols, row, col, peak_height,
                            higher_tolerance, xres, yres,
                        )
                        if dominance is None:
                            status = "no_higher_terrain_in_dem"
                        else:
                            saddle_low, saddle_high, island_edge, error = saddle_interval(
                                values, rows, cols, neighbour_offsets, levels,
                                index, peak_height, higher_tolerance,
                            )
                            if error:
                                status = error
                            else:
                                prominence_low = max(0.0, peak_height - saddle_high)
                                prominence_high = max(0.0, peak_height - saddle_low)
                                dominance_edge = dominance > edge_distance
                                status = (
                                    "edge_relevant"
                                    if island_edge or dominance_edge
                                    else "ok"
                                )
                                article_values = [
                                    e_value(peak_height, dominance, prominence_low),
                                    e_value(peak_height, dominance, prominence_high),
                                ]
                                code_values = [
                                    e_value(peak_height, dominance, prominence_low, True),
                                    e_value(peak_height, dominance, prominence_high, True),
                                ]
                                if None not in article_values:
                                    e_article_low, e_article_high = sorted(article_values)
                                    e_code_low, e_code_high = sorted(code_values)
                                    if dominance < 100000.0:
                                        e_note = "article_uses_d; historic_code_omits_d"
                                    elif dominance > 100000.0:
                                        e_note = "article_omits_d; historic_code_uses_d"
                                    else:
                                        e_note = "100km_boundary: article rule uses no d term"

            result.setGeometry(geometry)
            result.setAttributes(
                attributes
                + [
                    "peak_{0}".format(feature_number + 1),
                    snap_distance,
                    peak_height,
                    edge_distance,
                    dominance,
                    saddle_low,
                    saddle_high,
                    prominence_low,
                    prominence_high,
                    e_article_low,
                    e_article_high,
                    e_code_low,
                    e_code_high,
                    e_note,
                    status,
                ]
            )
            sink.addFeature(result, QgsFeatureSink.FastInsert)

            feedback.pushInfo("peak_{0}: {1}".format(feature_number + 1, status))
            feedback.setProgress(int((feature_number + 1) * 100 / total))

        return {self.OUTPUT: destination}

    def createInstance(self):
        return PerfectPeakMetrics()

