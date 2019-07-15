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

def iterpairs(l):
    """
    Fast iterator for pairs of a list.
    """
    # itertools.combinations() apparently *sorts* its input! This is
    # unacceptable for us when we are trying to pack our structures.
    for i, x in enumerate(l):
        for j in range(i + 1, len(l)):
                yield x, l[j]

def itertilted(m, n):
    for i in range(m + n - 1):
        j = i - (m - 1) if i > m - 1 else 0
        i -= j
        assert i < m
        yield i, j
        while i and j < n - 1:
            i -= 1
            j += 1
            yield i, j


def dot2png(dot):
    text = "digraph " + dot
    p = Popen(["dot", "-Tpng"], stdin=PIPE, stdout=PIPE)
    stdout, stderr = p.communicate(text.encode("utf-8"))
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

ZAHA_CHUNK_TYPE = "zaHa"

def packPNG(dot, metadata):
    png = dot2png(dot)
    chunks = [(ty, chunk) for ty, chunk in iterchunks(png)]
    blob = json.dumps(metadata)
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

def succinct(dag, size):
    acc = 0
    for i, (u, v) in enumerate(iterpairs(range(size))):
        if v in dag[u]:
            acc |= 1 << i
    return acc

def reduceDAG(dag):
    def downward(u, v, _cache={}):
        k = u, v
        if k not in _cache:
            rv = False
            seen = set()
            queue = list(dag.get(u, ()))
            while queue:
                n = queue.pop()
                if n in seen:
                    continue
                seen.add(n)
                if n == v:
                    rv = True
                    break
                queue.extend(dag.get(n, ()))
            _cache[k] = rv
        return _cache[k]

    for u, vs in dag.iteritems():
        # Remove self-loops here.
        vs.discard(u)
        # Order doesn't matter here, so itertools.combinations() is safe.
        for v1, v2 in combinations(vs.copy(), 2):
            if downward(v1, v2):
                vs.discard(v2)
            elif downward(v2, v1):
                vs.discard(v1)
    return dag


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

def upperTriangular(i):
    # NB: Triangular number formula, always integer
    return (i * (i - 1)) // 2

def flip(size, structure):
    cols = [[] for _ in range(size)]
    intSize = upperTriangular(size)
    ints = range(intSize)
    for i in range(size):
        for j in range(i):
            cols[j].append(ints.pop())
    perm = sum(cols, [])
    # print "perm inverts self", [perm[i] for i in perm]

    rv = 0
    for i in range(intSize):
        if structure & (1 << i):
            rv |= 1 << perm[i]
    return rv

@attr.s
class Pos(object):
    labels = attr.ib()
    structure = attr.ib()
    title = attr.ib()

    @classmethod
    def fromDCG(cls, labels, dcg, title):
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
        dag = reduceDAG(dag)
        s = succinct(dag, len(ks))
        self = cls(labels=ks, structure=s, title=title)
        return self

    def makeDOT(self):
        lines = [
            u'labelloc="t";',
            u'label="%s";' % (self.title.replace('"', '\\"'),),
        ]
        labels = [l.replace('"', '\\"') for l in self.labels]
        for label in labels:
            lines.append(u'"%s";' % label)
        for i, (u, v) in enumerate(iterpairs(labels)):
            if self.structure & (1 << i):
                lines.append(u'"%s" -> "%s";' % (u, v))
        dot = u"{" + u"\n".join(lines) + u"}"
        return dot

    def metadata(self):
        d = attr.asdict(self)
        d.update({
            "v": 2,
            "cat": "Pos",
        })
        return d

    def makePNG(self):
        dot = self.makeDOT()
        return packPNG(dot, self.metadata())

    def address(self, u, v):
        l = len(self.labels)
        if u >= v or l <= u or l <= v:
            raise Exception("oob on %d: %d, %d" % (l, u, v))
        # The addressing scheme is like a regular 2D bitarray, except that
        # each u-row is smaller than the last.
        return sum(range(l - u - 1, l - 1)) + v - 1

    def hasArrow(self, u, v):
        if u > v:
            rv = False
        elif u == v:
            rv = True
        else:
            rv = bool(self.structure & (1 << self.address(u, v)))
        return rv

    def hasPath(self, u, v, _cache={}):
        k = self.structure, u, v
        if k not in _cache:
            if self.hasArrow(u, v):
                _cache[k] = True
            else:
                vs = [i for i in range(u + 1, v) if self.hasArrow(u, i)]
                _cache[k] = any(self.hasPath(i, v) for i in vs)
        return _cache[k]

    def iterarrows(self):
        for i, (u, v) in enumerate(iterpairs(range(len(self.labels)))):
            if self.structure & (1 << i):
                yield u, v

    def reduce(self):
        # Build a DAG.
        dag = defaultdict(set)
        for u, v in self.iterarrows():
            dag[u].add(v)
        # Reduce that DAG.
        dag = reduceDAG(dag)
        # All done.
        s = succinct(dag, len(self.labels))
        return Pos(labels=self.labels, structure=s, title=self.title)

    def dual(self):
        # Strategy: Reverse the labels and transpose the matrix.
        labels = self.labels[:]
        labels.reverse()
        structure = flip(len(labels), self.structure)
        title = u"Dual of " + self.title
        return Pos(labels=labels, structure=structure, title=title)

    def sum(self, other):
        # Insight: We don't need any new arrows!
        # We will shift our two bundles of arrows. One bundle is shifted
        # against the grain of the encoding, and the other with the grain.
        ls = self.labels + other.labels
        # With the grain is easy.
        width = sum(range(len(other.labels), len(ls)))
        s = other.structure << width
        # We cannot work against the grain, so instead we take bitslices along
        # the grain and copy them into position, like a blit. Our slices are
        # "going backwards", so we need the -1 offsets to count backwards.
        acc = self.structure
        maskSize = len(self.labels) - 1
        offset = 0
        stride = len(ls) - 1
        while maskSize:
            slice = (acc & ((2 ** maskSize) - 1)) << offset
            s |= slice
            acc >>= maskSize
            maskSize -= 1
            offset += stride
            stride -= 1
        title = self.title + u" + " + other.title
        return Pos(labels=ls, structure=s, title=title)

    def product(self, other):
        slen = len(self.labels)
        olen = len(other.labels)
        tilted = list(itertilted(slen, olen))
        ls = []
        for l, r in tilted:
            s = self.labels[l] + "*" + other.labels[r]
            ls.append(s)
        s = 0
        pairs = iterpairs(tilted)
        for i, ((su, ou), (sv, ov)) in enumerate(pairs):
            if self.hasArrow(su, sv) and other.hasArrow(ou, ov):
                s |= 1 << i
        title = self.title + u" * " + other.title
        return Pos(labels=ls, structure=s, title=title).reduce()

    def links(self):
        return [pair for i, pair in enumerate(iterpairs(self.labels))
                if self.structure & (1 << i)]

    def matrix(self):
        offset = 0
        rv = []
        stride = len(self.labels)
        for row in range(stride):
            chars = []
            for i in range(stride):
                if i < row:
                    chars.append(' ')
                elif i == row:
                    chars.append('\\')
                else:
                    if self.structure & (1 << offset):
                        chars.append('#')
                    else:
                        chars.append('-')
                    offset += 1
            rv.append("".join(chars))
        return rv

def defrost(d):
    v = d.pop("v")
    if v == 1:
        d["title"] = "Untitled Diagram"
        v = 2
    elif v == 2:
        pass
    else:
        raise ValueError("Unknown diagram version %d" % v)
    cat = d.pop("cat")
    if cat == "Functor":
        source = defrost(d.pop("source"))
        target = defrost(d.pop("target"))
        return Functor(source=source, target=target, **d)
    elif cat == "Pos":
        return Pos(**d)
    else:
        raise ValueError(cat)

def getDiagram(bs):
    d = getPayload(bs)
    return defrost(d)

@attr.s
class Functor(object):
    source = attr.ib()
    target = attr.ib()
    map = attr.ib()
    title = attr.ib()

    def makeDOT(self):
        s = self.source.makeDOT()
        t = self.target.makeDOT()
        lines = [
            u"{",
            u"subgraph cluster_lhs " + s,
            u"subgraph cluster_rhs " + t,
            u'labelloc="t";',
            u'label="%s";' % (self.title,),
        ]
        for k, v in self.map.iteritems():
            lines.append(u'"%s" -> "%s";' % (k, v))
        lines.append(u"}")
        dot = u"\n".join(lines)
        return dot

    def metadata(self):
        d = attr.asdict(self)
        d.update({
            "v": 2,
            "cat": "Functor",
            "source": self.source.metadata(),
            "target": self.target.metadata(),
        })
        return d

    def makePNG(self):
        dot = self.makeDOT()
        return packPNG(dot, self.metadata())

@click.group()
def cli():
    pass

@cli.command()
@click.option("--expr", prompt=True)
@click.option("--title", prompt=True)
@click.option("--amend/--fresh", default=False)
def poset(expr, title, amend):
    dcg, labels = parseChains(expr)
    d = Pos.fromDCG(labels, dcg, title)
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.argument("diagram", type=click.File("rb"))
def relabel(diagram):
    d = getDiagram(diagram.read())
    old = [d.title] + d.labels
    text = click.edit(text="\n".join(old))
    new = [l.strip() for l in text.split("\n") if l.strip()]
    if len(new) != len(old):
        raise ValueError("Incorrect number of labels")
    d.title = new[0]
    d.labels = new[1:]
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.argument("diagram", type=click.File("rb"))
def describe(diagram):
    d = getPayload(diagram.read())
    print json.dumps(d)
    d = defrost(d)
    for label in d.labels:
        print label,
    print ''
    for line in d.matrix():
        print line

@cli.command(name="json")
@click.argument("diagram", type=click.File("rb"))
def _json(diagram):
    d = getDiagram(diagram.read())
    print json.dumps(attr.asdict(d))

@cli.command()
@click.argument("diagram", type=click.File("rb"))
def redraw(diagram):
    d = getDiagram(diagram.read())
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.argument("diagram", type=click.File("rb"))
def dual(diagram):
    """
    Turn around, or flip, every arrow in a diagram.
    """
    d = getDiagram(diagram.read())
    d = d.dual()
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command(name="sum")
@click.argument("lhs", type=click.File("rb"))
@click.argument("rhs", type=click.File("rb"))
def _sum(lhs, rhs):
    """
    Take the sum, or coproduct, of two diagrams.
    """
    l = getDiagram(lhs.read())
    r = getDiagram(rhs.read())
    # We can symmetrically go in either direction. This is the direction that
    # Python would choose if we used operator overloading and wrote `l + r`.
    d = l.sum(r)
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command(name="product")
@click.argument("lhs", type=click.File("rb"))
@click.argument("rhs", type=click.File("rb"))
def _product(lhs, rhs):
    """
    Take the product of two diagrams.
    """
    l = getDiagram(lhs.read())
    r = getDiagram(rhs.read())
    # Dual to sums.
    d = l.product(r)
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.argument("diagrams", nargs=-1, type=click.File("rb"))
def union(diagrams):
    """
    Take the union of many diagrams.
    """

    # Build the union.
    dcg = defaultdict(set)
    relabels = {}
    labels = []
    isos = []
    # Eagerly read in everything so we can close the files and have the
    # diagrams in memory.
    posets = [getDiagram(diagram.read()) for diagram in diagrams]
    for poset in posets:
        broadcasts = []
        for label in poset.labels:
            # We broadcast each member of an isomorphic label, since we're
            # taking unions by label.
            broadcasts.append(set())
            if u"≅" in label:
                pieces = label.split(u"≅")
                isos.append(pieces)
            else:
                pieces = label,
            for l in pieces:
                if l not in relabels:
                    relabels[l] = len(labels)
                    labels.append(l)
                broadcasts[-1].add(relabels[l])
        for u, v in poset.iterarrows():
            for i in broadcasts[u]:
                for j in broadcasts[v]:
                    dcg[i].add(j)
    # And, for each isomorphism, add all the autos to the DCG as well.
    for iso in isos:
        us = [relabels[l] for l in iso]
        for u in us:
            for v in us:
                dcg[u].add(v)

    if len(posets) == 1:
        title = posets[0].title
    elif len(posets) == 2:
        title = posets[0].title + u" ∪ " + posets[1].title
    elif len(posets) <= 5:
        title = u"⋃ " + u", ".join(p.title for p in posets)
    else:
        title = u"⋃ %d diagrams" % (len(posets),)

    d = Pos.fromDCG(labels, dcg, title)
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

class FunctorTable(object):
    def __init__(self, source, target, identity=False):
        rv = {}
        if identity:
            for label in source.labels:
                if label in target.labels:
                    rv[label] = set([label])
        else:
            for label in source.labels:
                rv[label] = set(target.labels)
        self.table = rv
        self.source = source
        self.target = target
        self.ss = {k:i for (i, k) in enumerate(source.labels)}
        self.ts = {k:i for (i, k) in enumerate(target.labels)}

    def viable(self):
        return all(bool(v) for v in self.table.itervalues())

    def restrict(self, restrictions):
        # NB: Consumes input list.
        while restrictions:
            rk, rvs = restrictions.pop()
            drk = self.table[rk]
            if drk.issubset(rvs):
                continue
            drk.intersection_update(rvs)
            ssrk = self.ss[rk]
            tsus = set(self.ts[rv] for rv in rvs)
            for arrow in self.source.iterarrows():
                if ssrk == arrow[0]:
                    nk = self.source.labels[arrow[1]]
                    nrvs = set(dv for dv in self.table[nk] if
                            any(self.target.hasPath(du, self.ts[dv]) for du in tsus))
                    restrictions.append((nk, nrvs))
                elif ssrk == arrow[1]:
                    nk = self.source.labels[arrow[0]]
                    nrvs = set(dv for dv in self.table[nk] if
                            any(self.target.hasPath(self.ts[dv], du) for du in tsus))
                    restrictions.append((nk, nrvs))

    def restrictSingle(self, k, choice):
        self.restrict([(k, set([choice]))])

    def restrictSet(self, k, choices):
        self.restrict([(k, choices)])

    def extractMap(self):
        # Destructive.
        rv = {}
        for k, v in self.table.iteritems():
            if len(v) != 1:
                raise ValueError(k)
            rv[k] = v.pop()
        return rv

@cli.command()
@click.option("--id", "data", flag_value="id")
@click.option("--title")
@click.argument("source", type=click.File("rb"))
@click.argument("target", type=click.File("rb"))
def functor(data, title, source, target):
    s = getDiagram(source.read())
    t = getDiagram(target.read())
    # Build the functor dict of possibilities.
    ft = FunctorTable(s, t, identity=(data == "id"))
    d = ft.table
    # As long as there is an ambiguity, resolve it.
    longs = sum(len(v) > 1 for v in d.itervalues())
    while longs:
        longs = sum(len(v) > 1 for v in d.itervalues())
        print longs, "objects left"
        for k, v in d.iteritems():
            if len(v) == 0:
                raise ValueError(k)
            elif len(v) == 1:
                continue
            blank = object()
            # Click bug can't print Unicode-laden options.
            print "Options:", u" ".join(v)
            choice = click.prompt(k + u" (blank to skip)", default=blank)
            while choice not in v and choice is not blank:
                print "Choice not in set; try again."
                choice = click.prompt(k + u" (blank to skip)")
            if choice is blank:
                continue
            # Now recursively check each assignment, node by node, to ensure
            # that it's still a functor.
            ft.restrictSingle(k, choice)
            break

    m = ft.extractMap()
    if title is None:
        title = s.title + u" → " + t.title
    f = Functor(source=s, target=t, map=m, title=title)
    png = f.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.option("--left/--right", default=False)
@click.option("--title")
@click.argument("diagram", type=click.File("rb"))
def adjoint(left, title, diagram):
    f = getDiagram(diagram.read())
    ft = FunctorTable(f.target, f.source)
    # if left, q ≤ f(g(q)), else f(g(q)) ≤ q
    for q in ft.source.labels:
        if left:
            ps = {p for p in ft.table[q]
                    if ft.source.hasPath(ft.ss[q], ft.ss[f.map[p]])}
        else:
            ps = {p for p in ft.table[q]
                    if ft.source.hasPath(ft.ss[f.map[p]], ft.ss[q])}
        ft.restrictSet(q, ps)
    # if left, g(f(p)) ≤ p, else p ≤ g(f(p))
    for p in ft.target.labels:
        q = f.map[p]
        if left:
            ps = {pp for pp in ft.table[q]
                    if ft.target.hasPath(ft.ts[pp], ft.ts[p])}
        else:
            ps = {pp for pp in ft.table[q]
                    if ft.target.hasPath(ft.ts[p], ft.ts[pp])}
        ft.restrictSet(q, ps)
    if not ft.viable():
        raise Exception("No viable functors are adjoint")
    map = ft.extractMap()
    if title is None:
        title = ("Left" if left else "Right") + " Adjoint to " + f.title
    f = Functor(source=f.target, target=f.source, map=map, title=title)
    png = f.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

@cli.command()
@click.option("--expr", prompt=True)
@click.option("--title", prompt=True)
def cat(expr, title):
    objs = []
    arrs = []
    for val in expr.split(";"):
        if ":" in val:
            name, ty = val.split(":")
            source, target = ty.split(u"→")
            arrs.append((name.strip(), source.strip(), target.strip()))
        else:
            objs.append(val.strip())
    labels = objs[:]
    objs = {o:i for i, o in enumerate(objs)}
    # Identity arrows for each object.
    arrows = {(i, i):i for i in range(len(labels))}
    for name, source, target in arrs:
        s = objs[source]
        t = objs[target]
        n = len(labels)
        labels.append(name)
        # Composition for each end of the arrow.
        arrows[s, n] = s
        arrows[n, t] = t
    import pdb; pdb.set_trace()
    d = {
        "labels": ["X", "Y", "Z", "f", "g"],
        "structure": 0,
        "title": "demo",
    }
    png = d.makePNG()
    with open("latest.png", "wb") as handle:
        handle.write(png)

if __name__ == "__main__":
    register_repl(cli)
    cli()
