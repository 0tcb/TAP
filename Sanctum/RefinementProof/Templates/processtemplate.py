#! /usr/bin/python3

from string import Template
from sys import exit
import argparse

def strip_spaces(l):
    lr = l.replace('  ', ' ')
    while lr != l:
        l = lr
        lr = l.replace('  ', ' ')
    return lr

def getAssertions(f):
    current_line = ''
    lines = []
    for line in f:
        line = line.strip()
        if len(line) == 0 or line.startswith(r'//'):
            continue
        words = line.split()
        if words[0] == 'assert':
            if len(current_line):
                lines.append(strip_spaces(current_line))
            current_line = ' '.join(words[1:])
        else:
            current_line += (' ' + line)

    return lines

def readRelation(filename):
    with open(filename, 'rt') as f:
        return getAssertions(f)

def rewriteRelations(i, t, relations):
    return ['%s%s %s' % (i, t, r) for r in relations]

def rewriteFile(relations, f):
    outputLines = []
    marker = r'//__TEMPLATE_INSERT__'
    for line in f:
        l = line.strip()
        if l.startswith(marker):
            words = l.split()
            pos = line.find(marker)
            assert pos != -1
            indent = ' '*pos
            if len(words) != 2:
                raise IOError("Invalid line format: '%s'" % line.rstrip())
            else:
                outputLines += rewriteRelations(indent, words[1], relations)
        else:
            outputLines.append(line.rstrip())
    return '\n'.join(outputLines)

def writeOutput(outputFilename, output):
    with open(outputFilename, 'wt') as f:
        print (output, file=f)

def rewriteInput(relations, inputFilename, outputFilename):
    with open(inputFilename, 'rt') as f:
        output = rewriteFile(relations, f)
        writeOutput(outputFilename, output)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="File to process.")
    parser.add_argument("output", help="Output filename.")
    parser.add_argument("--template", 
            default="RefinementRelation.bpl", help="Refinement relation.")
    args = parser.parse_args()

    try:
        relations = readRelation(args.template)
        rewriteInput(relations, args.input, args.output)
    except IOError as e:
        print ('I/O error: %s' % str(e))

if __name__ == '__main__':
    main()
