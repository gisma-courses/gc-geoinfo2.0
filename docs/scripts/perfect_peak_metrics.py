"""
Perfect Peak Metrics

PyQGIS Processing script for QGIS 3.44+.

Input:  a projected DEM and either summit points or a summit mask.
Output: summit points with raster-based dominance, a saddle interval, a
        prominence interval, and an explicit validity status.

The algorithm intentionally does NOT calculate the historic perfectPeak
independence (E) value. Its domain-specific rule must be documented before it
is used in teaching or assessment.
"""

from bisect import bisect_right
from collections import deque
from math import floor, hypot

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
    QgsProcessingParameterRasterLayer,
    QgsWkbTypes,
)
from qgis.PyQt.QtCore import QVariant


class PerfectPeakMetrics(QgsProcessingAlgorithm):
    DEM = "DEM"
    SUMMITS = "SUMMITS"
    PEAK_MASK = "PEAK_MASK"
    HIGHER_TOLERANCE = "HIGHER_TOLERANCE"
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

        Der Status edge_relevant bedeutet: Die relevante Zusammenhangsfläche
        berührt den DGM-Rand. Das Ergebnis ist dann nur ausschnittsbezogen.
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

        if connectivity == 0:
            neighbour_offsets = ((-1, 0), (1, 0), (0, -1), (0, 1))
        else:
            neighbour_offsets = (
                (-1, 0), (-1, 1), (0, 1), (1, 1),
                (1, 0), (1, -1), (0, -1), (-1, -1),
            )

        out_fields = QgsFields(source.fields()) if source is not None else QgsFields()
        for name, field_type in (
            ("pp_id", QVariant.String),
            ("peak_h_m", QVariant.Double),
            ("dominanz_m", QVariant.Double),
            ("scharte_lo", QVariant.Double),
            ("scharte_hi", QVariant.Double),
            ("prom_lo_m", QVariant.Double),
            ("prom_hi_m", QVariant.Double),
            ("pp_status", QVariant.String),
        ):
            out_fields.append(QgsField(name, field_type, "", 32, 3))

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
        features = list(source.getFeatures()) if source is not None else []

        def cell_for_point(point):
            col = int(floor((point.x() - extent.xMinimum()) / xres))
            row = int(floor((extent.yMaximum() - point.y()) / yres))
            if row < 0 or row >= rows or col < 0 or col >= cols:
                return None
            return row, col, row * cols + col

        def nearest_higher_distance(row, col, height):
            """Distance between raster-cell centres, matching GDAL proximity."""
            best = None
            for index, value in enumerate(values):
                if value is None or value <= height + higher_tolerance:
                    continue
                other_row, other_col = divmod(index, cols)
                distance = hypot((other_col - col) * xres, (other_row - row) * yres)
                if best is None or distance < best:
                    best = distance
            return best

        def connected_to_higher(start_index, summit_height, threshold):
            """Return whether the threshold component reaches higher terrain.

            The second return value records whether this component touches the
            DGM boundary. A boundary contact means that the regional result may
            change when the raster is extended.
            """
            if values[start_index] is None or values[start_index] < threshold:
                return False, False

            seen = bytearray(cell_count)
            queue = deque([start_index])
            seen[start_index] = 1
            touches_edge = False

            while queue:
                index = queue.popleft()
                row, col = divmod(index, cols)
                if row == 0 or row == rows - 1 or col == 0 or col == cols - 1:
                    touches_edge = True
                if values[index] > summit_height + higher_tolerance:
                    return True, touches_edge

                for dr, dc in neighbour_offsets:
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
            return False, touches_edge

        def saddle_interval(start_index, summit_height):
            """Find the highest DGM level still connecting to higher terrain."""
            maximum_level_index = bisect_right(levels, summit_height) - 1
            if maximum_level_index < 0:
                return None, None, None, "invalid_summit_height"

            connected, _ = connected_to_higher(
                start_index, summit_height, levels[0]
            )
            if not connected:
                return None, None, None, "disconnected_in_raster"

            low, high, best = 0, maximum_level_index, 0
            while low <= high:
                middle = (low + high) // 2
                connected, _ = connected_to_higher(
                    start_index, summit_height, levels[middle]
                )
                if connected:
                    best = middle
                    low = middle + 1
                else:
                    high = middle - 1

            saddle_low = levels[best]
            saddle_high = (
                levels[best + 1]
                if best + 1 <= maximum_level_index
                else summit_height
            )
            _, touches_edge = connected_to_higher(
                start_index, summit_height, saddle_low
            )
            status = "edge_relevant" if touches_edge else "ok"
            return saddle_low, saddle_high, status, None

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
            result.setGeometry(feature.geometry())
            attributes = feature.attributes()
            peak_height = dominance = saddle_low = saddle_high = None
            prominence_low = prominence_high = None
            status = "invalid_geometry"

            if feature.hasGeometry() and not feature.geometry().isEmpty():
                point = feature.geometry().asPoint()
                if transform is not None:
                    point = transform.transform(point)
                cell = cell_for_point(point)
                if cell is None:
                    status = "outside_dem"
                else:
                    row, col, index = cell
                    peak_height = values[index]
                    if peak_height is None:
                        status = "nodata_cell"
                    else:
                        dominance = nearest_higher_distance(row, col, peak_height)
                        if dominance is None:
                            status = "no_higher_terrain_in_dem"
                        else:
                            saddle_low, saddle_high, saddle_status, error = saddle_interval(
                                index, peak_height
                            )
                            if error:
                                status = error
                            else:
                                prominence_low = max(0.0, peak_height - saddle_high)
                                prominence_high = max(0.0, peak_height - saddle_low)
                                status = saddle_status

            result.setAttributes(
                attributes
                + [
                    "peak_{0}".format(feature_number + 1),
                    peak_height,
                    dominance,
                    saddle_low,
                    saddle_high,
                    prominence_low,
                    prominence_high,
                    status,
                ]
            )
            sink.addFeature(result, QgsFeatureSink.FastInsert)

            feedback.pushInfo("peak_{0}: {1}".format(feature_number + 1, status))
            feedback.setProgress(int((feature_number + 1) * 100 / total))

        return {self.OUTPUT: destination}

    def createInstance(self):
        return PerfectPeakMetrics()

