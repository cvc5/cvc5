#!/usr/bin/env python3

import argparse
import glob
import gzip
import json
import logging
import re
from sklearn import linear_model
import statistics


def parse_commandline():
    """Parse commandline arguments"""
    epilog = """
This script can be used to compute good resource weights based on benchmark
results. The resource weights are used by cvc5 to approximate the running time
by the spent resources, multiplied with their weights.

In the first stage ("parse") this script reads the output files of a benchmark
run as generated on our cluster. The output files are expected to be named
"*.smt2/output.log" and should contain the statistics (by use of "--stats").
The result is a gziped json file that contains all the relevant information
in a compact form.

In the second stage ("analyze") this script loads the gziped json file and uses
a linear regression model to learn resource weights. The resulting weights can
be used as constants for the resource options ("--*-step=n"). Additionally,
this script performs some analysis on the results to identify outliers where
the linear model performs particularly bad, i.e., the runtime estimation is way
off.
    """
    usage = """
    first stage to parse the solver output:
    %(prog)s parse <output directory>
    
    second stage to learn resource weights:
    %(prog)s analyze
    """
    parser = argparse.ArgumentParser(description='export and analyze resources from statistics',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter,
                                     epilog=epilog,
                                     usage=usage)
    parser.add_argument('command', choices=[
                        'parse', 'analyze'], help='task to perform')
    parser.add_argument('basedir', default=None, nargs='?',
                        help='path of benchmark results')
    parser.add_argument('-v', '--verbose',
                        action='store_true', help='be more verbose')
    parser.add_argument('--json', default='data.json.gz',
                        help='path of json file')
    parser.add_argument('--threshold', metavar='SEC', type=int, default=1,
                        help='ignore benchmarks with a runtime below this threshold')
    parser.add_argument('--mult', type=int, default=1000,
                        help='multiply running times with this factor for regression')

    return parser.parse_args()


def load_zipped_json(filename):
    """Load data from a gziped json file"""
    with gzip.GzipFile(args.json, 'r') as fin:
        return json.loads(fin.read().decode('utf-8'))


def save_zipped_json(filename, data):
    """Store data to a gziped json file"""
    with gzip.GzipFile(args.json, 'w') as fout:
        fout.write(json.dumps(data).encode('utf-8'))


def get_sorted_values(data):
    """Transform [['name', value], ...] to [value, ...] sorted by names"""
    return [d[1] for d in sorted(data)]


def parse(args):
    if args.basedir is None:
        raise Exception('Specify basedir for parsing!')
    filename_re = re.compile('(.*\\.smt2)/output\\.log')
    resource_re = re.compile('resource::([^,]+), ([0-9]+)')
    result_re = re.compile('driver::sat/unsat, ([a-z]+)')
    totaltime_re = re.compile('driver::totalTime, ([0-9\\.]+)')

    logging.info('Parsing files from {}'.format(args.basedir))
    data = {}
    failed = 0
    for file in glob.iglob('{}/**/output.log'.format(args.basedir), recursive=True):
        content = open(file).read()
        try:
            filename = filename_re.match(file).group(1)
            r = resource_re.findall(content)
            r = list(map(lambda x: (x[0], int(x[1])), r))
            data[filename] = {
                'resources': r,
                'result': result_re.search(content).group(1),
                'time': float(totaltime_re.search(content).group(1)),
            }
        except Exception as e:
            logging.debug('Failed to parse {}: {}'.format(file, e))
            failed += 1

    if failed > 0:
        logging.info('Failed to parse {} out of {} files'.format(
            failed, failed + len(data)))
    logging.info('Dumping data to {}'.format(args.json))
    save_zipped_json(args.json, data)


def analyze(args):
    logging.info('Loading data from {}'.format(args.json))
    data = load_zipped_json(args.json)

    logging.info('Extracting resources')
    resources = set()
    for f in data:
        for r in data[f]['resources']:
            resources.add(r[0])
    resources = list(sorted(resources))

    vals = {r: [] for r in resources}

    logging.info('Collecting data from {} benchmarks'.format(len(data)))
    x = []
    y = []
    for filename in data:
        d = data[filename]
        if d['time'] < args.threshold:
            continue
        x.append(get_sorted_values(d['resources']))
        y.append(d['time'] * args.mult)

        for r in d['resources']:
            vals[r[0]].append(r[1])

    logging.info('Training regression model')
    clf = linear_model.LinearRegression()
    r = clf.fit(x, y)
    coeffs = zip(resources, r.coef_)
    for c in sorted(coeffs, key=lambda c: c[1]):
        minval = min(vals[c[0]])
        maxval = max(vals[c[0]])
        avgval = statistics.mean(vals[c[0]])
        medval = statistics.median(vals[c[0]])
        impact = c[1] * avgval
        logging.info('{:23}-> {:15.10f}\t({} .. {:10}, avg {:9.2f}, med {:8}, impact {:7.3f})'.format(
            *c, minval, maxval, avgval, medval, impact))

    logging.info('Comparing regression model with reality')
    outliers = {
        'over-estimated': [],
        'under-estimated': []
    }
    for filename in data:
        d = data[filename]
        actual = d['time']
        if actual < args.threshold:
            continue
        vals = get_sorted_values(d['resources'])
        predict = float(r.predict([vals])) / args.mult
        outliers['over-estimated'].append([predict / actual, predict, actual, filename])
        outliers['under-estimated'].append([actual / predict, predict, actual, filename])

    for out in outliers:
        logging.info('Showing outliers for {}'.format(out))
        filtered = outliers[out]
        for vals in sorted(filtered)[-5:]:
            logging.info(
                '  -> {:6.2f} ({:6.2f}, actual {:6.2f}): {}'.format(*vals))

    cur = 0
    gnuplot = open('plot.data', 'w')
    for out in sorted(outliers['under-estimated']):
        gnuplot.write('{}\t{}\n'.format(cur, out[0]))
        cur += 1


if __name__ == "__main__":
    logging.basicConfig(format='[%(levelname)s] %(message)s')
    args = parse_commandline()
    if args.verbose:
        logging.getLogger().setLevel(level=logging.DEBUG)
    else:
        logging.getLogger().setLevel(level=logging.INFO)
    if args.command == 'parse':
        parse(args)
    elif args.command == 'analyze':
        analyze(args)
