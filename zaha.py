#!/usr/bin/env nix-shell
# encoding: utf-8
#! nix-shell -p graphviz pythonPackages.attrs pythonPackages.click-repl -i python

from collections import defaultdict
from itertools import combinations
import json
from struct import Struct
from subprocess import CalledProcessError, PIPE, Popen

import attr

import click
from click_repl import register_repl

def dot2png(text):
    p = Popen(["dot", "-Tpng"], stdin=PIPE, stdout=PIPE)
    stdout, stderr = p.communicate(text)
    status = p.poll()
    if status:
        raise CalledProcessError(status, "dot", output=stdout)
    return stdout

# CRC computation, from http://libpng.org/pub/png/spec/1.2/PNG-CRCAppendix.html

def _table(n):
    c = n
    for k in range(8):
        if c & 1:
            c = 0xedb88320 ^ (c >> 1)
        else:
            c >>= 1
    return c
CRC_TABLE = [_table(n) for n in range(0x100)]
def _crc(h, s):
    for c in s:
        h = CRC_TABLE[(h ^ ord(c)) & 0xff] ^ (h >> 8)
    return h
def computeCRC(s):
    return _crc(0xffffffff, s) ^ 0xffffffff

LONG = Struct(">L")
MAGIC = "\x89PNG\r\n\x1a\n"

def iterchunks(png):
    offset = [0]
    def read(size, _offset=offset):
        start = _offset[0]
        stop = start + size
        _offset[0] = stop
        rv = png[start:stop]
        return rv
    sig = read(8)
    if sig != MAGIC:
        raise ValueError("Bad PNG signature: " + sig)
    while offset[0] < len(png):
        length, = LONG.unpack(read(4))
        ty = read(4)
        chunk = read(length)
        crc, = LONG.unpack(read(4))
        if crc != computeCRC(ty + chunk):
            raise ValueError("Bad CRC on chunk")
        yield ty, chunk

def buildChunk(ty, chunk):
    length = LONG.pack(len(chunk))
    body = ty + chunk
    crc = LONG.pack(computeCRC(body))
    return length + body + crc

def succinct2dot(labels, structure):
    lines = []
    for i, (u, v) in enumerate(combinations(labels, 2)):
        if structure & (1 << i):
            lines.append(u""""%s" -> "%s";""" % (u, v))
    return "digraph {" + u"\n".join(lines).encode("utf-8") + "}"

ZAHA_CHUNK_TYPE = "zaHa"

def makePNG(labels, structure):
    dot = succinct2dot(labels, structure)
    png = dot2png(dot)
    chunks = [(ty, chunk) for ty, chunk in iterchunks(png)]
    blob = json.dumps({
        "v": 1,
        "cat": "Pos",
        "labels": labels,
        "structure": structure,
    })
    chunks.insert(-1, (ZAHA_CHUNK_TYPE, blob))
    return MAGIC + "".join(buildChunk(ty, chunk) for ty, chunk in chunks)

def tarjan(graph):
    stack = []
    indices = {}
    links = {}
    rv = []

    def go(v, counter=[0]):
        indices[v] = links[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        for u in graph.get(v, []):
            if u not in indices:
                go(u)
                links[v] = min(links[v], links[u])
            elif u in stack:
                links[v] = min(links[v], indices[u])
        if links[v] == indices[v]:
            s = set()
            while True:
                u = stack.pop()
                s.add(u)
                if u == v:
                    break
            rv.append(s)

    for v in graph.iterkeys():
        if v not in indices:
            go(v)
    rv.reverse()
    return rv

@click.group()
def cli():
    pass

@cli.command()
def go():
    png = makePNG(["x", "y", "z"], 3)
    with open("latest.png", "wb") as handle:
        handle.write(png)

def succinct(dag, size):
    acc = 0
    for i, (u, v) in enumerate(combinations(range(size), 2)):
        if v in dag[u]:
            acc |= 1 << i
    return acc

def reduce(dag):
    for u, vs in dag.iteritems():
        # Remove self-loops here.
        vs.discard(u)
        for v1, v2 in combinations(vs.copy(), 2):
            if v2 in dag[v1]:
                vs.discard(v2)
            elif v1 in dag[v2]:
                vs.discard(v1)

def parseChains(expr):
    dcg = defaultdict(set)
    clabels = {}
    for chain in expr.split(";"):
        verts = [clabels.setdefault(v.strip(), len(clabels))
                 for v in chain.split(u"→")]
        for u, v in zip(verts, verts[1:]):
            dcg[u].add(v)
    labellist = sorted(clabels.iterkeys(), key=clabels.__getitem__)
    return dcg, labellist

def getPayload(bs):
    for ty, chunk in iterchunks(bs):
        if ty != ZAHA_CHUNK_TYPE:
            continue
        return json.loads(chunk)
    raise ValueError("Payload was missing %s chunk" % ZAHA_CHUNK_TYPE)

def flip(size, structure):
    cols = [[] for _ in range(size)]
    # NB: Triangular number formula, always integer
    intSize = (size * (size - 1)) // 2
    ints = range(intSize)
    for i in range(size):
        for j in range(i):
            cols[j].append(ints.pop())
    perm = sum(cols, [])
    print "size", size, "perm", perm
    print "perm inverts self", [perm[i] for i in perm]

    rv = 0
    for i in range(intSize):
        if structure & (1 << i):
            rv |= 1 << perm[i]
    return rv

@attr.s
class Pos(object):
    labels = attr.ib()
    structure = attr.ib()

    def makePNG(self):
        return makePNG(self.labels, self.structure)

    def dual(self):
        labels = self.labels[:]
        labels.reverse()
        structure = flip(len(labels), self.structure)
        return Pos(labels=labels, structure=structure)

def getDiagram(bs):
    d = getPayload(bs)
    v = d.pop("v")
    if v != 1:
        raise ValueError("Unknown diagram version %d" % v)
    d.pop("cat")
    return Pos(**d)

@cli.command()
@click.option("--expr", prompt=True)
def poset(expr):
    dcg, labels = parseChains(expr)
    sccs = tarjan(dcg)
    ks = [u"≅".join(labels[v] for v in sorted(scc)) for scc in sccs]
    # Build the DAG from DCG. First make labels from the SCCs. Then iterate
    # through the DCG and build the DAG.
    seen = {}
    for u, scc in enumerate(sccs):
        for old in scc:
            seen[old] = u
    dag = defaultdict(set)
    for u, vs in dcg.iteritems():
        dag[seen[u]].update(seen[v] for v in vs)
    reduce(dag)
    s = succinct(dag, len(ks))
    d = Pos(labels=ks, structure=s)
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.argument("diagram", type=click.File("rb"))
def describe(diagram):
    print getDiagram(diagram.read())

@cli.command()
@click.argument("diagram", type=click.File("rb"))
@click.argument("output", type=click.File("wb"))
def dual(diagram, output):
    """
    Turn around, or flip, every arrow in a diagram.
    """
    d = getDiagram(diagram.read())
    d = d.dual()
    png = d.makePNG()
    with output as handle:
        handle.write(png)

if __name__ == "__main__":
    register_repl(cli)
    cli()
