#!/usr/bin/env python
#
# Convert very simple svg files into ocaml data structures.
#
# In Inkscape:
# 1. Create a vector image.
# 2. Turn all objects into paths.
# 3. Extensions/Modify Path/Flatten Beziers... (1.0)
# 4. Run this script
#
import sys, re
from xml.sax import make_parser
from xml.sax.handler import ContentHandler

svgpath_to_list_re = re.compile(r'\s*?([ML]|[0-9.]+)',
                                re.MULTILINE | re.IGNORECASE)
float_re = re.compile(
    r'([LlmM]?)\s*([-+]?(?:(?:\d*\.\d+)|(?:\d+\.?))(?:[Ee][+-]?\d+)?)')
lead_digits_re = re.compile(r'\d+')

points_per_line = 3

def svgpath_to_lists(pathstr, scale=1.0):
    paths = []
    fst = None
    mode = ''

    (lx, ly) = (0, 0)
    path = []
    for ns in float_re.finditer(pathstr):
        m = ns.group(1).upper()
        n = int(round(float(ns.group(2)) * scale))

        if fst is None:
            fst = n
            mode = m
        else:
            if mode == 'M':
                if path != []: paths.append(path)
                path = []
            elif mode == 'L':
                pass
            else:
                fst = fst + lx
                n = ly + n

            path.append((fst, n))
            (lx, ly) = (fst, n)
            fst = None

    paths.append(path)
    return paths

def style_to_hash(style):
    r = {}
    for keyval in style.split(';'):
        keyval = keyval.split(':', 1)
        r[str(keyval[0].strip())] = str(keyval[1].strip())
    return r

def check_limits(((minx, miny), (maxx, maxy)), ((x1, y1), (x2, y2))):
    return ((min(minx, x1), min(miny, y1)), (max(maxx, x2), max(maxy, y2)))

def check_point(limits, point):
    return check_limits(limits, (point, point))

def midpoint((x1, y1), (x2, y2)):
    return (x1 + ((x2 - x1) / 2),
            y1 + ((y2 - y1) / 2))

def points_to_str(points):
    r = []
    limits = (points[0], points[0])

    for ((x, y), i) in zip(points, range(1, len(points) + 1)):
        r.append("(%d, %d); " % (x, y))
        if i % points_per_line == 0:
            r.append('\n                ')
        limits = check_point(limits, (x, y))

    return (limits, "".join(r))

class SVGContentHandler(ContentHandler):

    def __init__(self, scale):
        self.scale = scale
        self.limits = ((sys.maxint, sys.maxint), (-sys.maxint, -sys.maxint))

    def _printPath(self, fill, color, linewidth, points):
        print '    { color = `NAME "%s";' % color
        print '      fill = %s;' % fill
        print '      linewidth = %s;' % linewidth
        print '      points = [%s] };' % points

    def startElement(self,name,attrs):
        if name == 'g':
            print "open Simplevector"
            print "let data = {"
            print "components = ["

        elif name == 'path':
            style = style_to_hash(attrs.get('style'))
            d = attrs.get('d')

            if style['fill'] == 'none':
                fill = 'None'
            else:
                fill = 'Some (`NAME "%s")' % style['fill']

            for rawpoints in svgpath_to_lists(d, self.scale):
                (plimits, points) = points_to_str(rawpoints)
                self.limits = check_limits(self.limits, plimits)

                self._printPath(fill, style['stroke'], 
                    lead_digits_re.match(style['stroke-width']).group(0),
                    points)
        
    def endElement(self,name):
        if name == 'g':
            print "        ];"
            (minxy, maxxy) = self.limits
            (mx, my) = midpoint(minxy, maxxy)
            print "lower = (%d, %d);" % minxy
            print "upper = (%d, %d);" % maxxy
            print "scale = %d;" % self.scale
            print "pivot = (%d, %d);" % (mx, my)
            print "}"
            print

def transform_paths(filename, scale):
    handler = SVGContentHandler(scale)

    parser = make_parser()
    parser.setContentHandler(handler)

    parser.parse(open(filename))

def main():
    if len(sys.argv) > 1:
        transform_paths(sys.argv[1], 1000)

main()

