#!/usr/bin/env nr

# Implements Finis, Jan P., et al. "Rws-diff: flexible and efficient change
# detection in hierarchical data." Proceedings of the 22nd ACM international
# conference on Information & Knowledge Management. ACM, 2013.
# https://db.in.tum.de/~finis/papers/RWS-Diff.pdf

import algorithm, asyncdispatch, asyncfile, md5, mersenne, math, os, re,
       sequtils, sets, strutils, tables

const pathSep = "/"

type
  FloatVec = seq[float]
  FileInfoBundle = (string, seq[string])
  FileInfoBundleTable = TableRef[string, seq[string]]
  FileInfoBundleSet = HashSet[FileInfoBundle]
  FileInfoTree = TableRef[string, (HashSet[string], seq[(string, string)])]


### Pseudo-module-boundary: ingestion section
proc readHashes(filename: string) : Future[FileInfoBundleTable]
     {.async.} =
  # Not truly asynchronous.
  let file = openAsync(filename)
  let data = await readAll(file)
  close(file)

  let splitLines = filter(map(split(data, "\n"), splitWhitespace),
                           proc(sl: seq[string]): bool = len(sl) == 2)

  # Start by filtering out identical paths, in common case
  # Allows for lower dimensionality for similar results in
  # later RWS-Diff stages. One nuance involves cases which
  # have multiple paths having duplicate hashes especially
  # across the two datasets being compared. Thus, keep all
  # paths with a given hash together.
  result = newTable[string, seq[string]]()
  for hashPath in splitLines:
    let hash = hashPath[0]
    let path = @[hashPath[1]]
    if hasKey(result, hash):
      insert(result[hash], path)
    else:
      result[hash] = path

proc getFilteredHashes(filename1: string, filename2: string):
                      (FileInfoBundleSet, FileInfoBundleSet) =
  let pairsH0 = toSet(toSeq(pairs(waitFor readHashes(filename1))))
  let pairsH1 = toSet(toSeq(pairs(waitFor readHashes(filename2))))
  let pairsCommon = pairsH0 * pairsH1

  # Ignore unchanged portions. Many tree diff algorithms are O(n^2)
  # or worse, so keep simple case quick, and ease debugging, with a
  # pair of large trees with relatively few differences.
  result = (pairsH0 - pairsCommon, pairsH1 - pairsCommon)

## createHashPath and createHashDirTree modify same data structures;
## for refactoring purposes, they're coupled.
proc createHashPath(dirtree: FileInfoTree, hash: string, pathPrefix: string,
                    pathElements: seq[string]): void =
  if len(pathElements) == 0:
    discard
  elif len(pathElements) == 1:
    # Leaf node, file.
    insert(dirtree[pathPrefix][1], (hash, pathElements[0]))
  else:
    doAssert len(pathElements) >= 2
    # Directory. Create if necessary, based on thus far built-up path.
    incl(dirTree[pathPrefix][0], pathElements[0])
    let nextPath = pathPrefix & pathElements[0] & pathSep
    if not hasKey(dirtree, nextPath):
      dirTree[nextPath] = (toSet[string]([]), @[])
    createHashPath(dirtree, hash, nextPath, pathElements[1..^1])

proc sortHashTreeFiles(dirtree: FileInfoTree):
                      Future[void] {.async} =
  # This is why to put hash (or other similar properties) first in file-tuple.
  # It guarantees a useful sort order.
  for paths in keys(dirtree):
    dirtree[paths][1] = sorted(dirtree[paths][1], system.cmp)

proc createHashDirTree(hashes: FileInfoBundleSet): Future[FileInfoTree]
                      {.async.} =
  # Preprocessing for pq-gram creation, to enable depth-first
  # searching. Use tables rather than real tree structure, as
  # that more easily enables gradual construction without the
  # required step of first sorting the input (or buffering or
  # otherwise waiting for completion of iterating through the
  # hash data source).

  # This structure separates files from directories. Directories
  # simply consist of their path prefix, for further lookup, and
  # files point to their hash values, also strings. Tuples, with
  # only structural type matching, seem borderline, whether they
  # be labeled by field. pq-grams treat each distinctly.
  result = newTable[string, (HashSet[string], seq[(string, string)])]()
  result[pathSep] = (toSet[string]([]), @[])

  for hashPaths in items(hashes):
    let (hash, paths) = hashPaths
    # For each path, construct or add to relevant table on demand,
    # to allow arbitrary input order of paths.
    for path in paths:
      # "/" is notional root within internal representation. Works with
      # absolute paths in *nix/MacOS and Windows, and relative paths as
      # long as one first strips leading "/" from input paths.
      #
      # Perhaps should allow '\' as well, but this is the only separator
      # which applies, across all modern, common OSes, and is guaranteed
      # to be a reserved element (including Windows).
      let pathElements = filter(split(replace(path, "^/+", ""), pathSep),
                                 proc(s: string) : bool = len(s) > 1)

      createHashPath(result, hash, pathSep, pathElements)

  # Sort file but not directory entries; this removes spurious differences in
  # pq-grams, which matters increasingly with larger $q$.
  await sortHashTreeFiles(result)


### Pseudo-module-boundary: math section
proc getMersenneFloat(m: var MersenneTwister): float =
  result = float(getNum(m))/float(high(uint32))*TAU

proc isClose(a: float, b: float): bool =
  # https://docs.scipy.org/doc/numpy/reference/generated/numpy.isclose.html
  const rtol = 1e-05
  const atol = 1e-08
  result = abs(a - b) <= (atol + rtol * abs(b))

proc genUnitSpherePoint(seed: uint32): FloatVec =
  var mt = newMersenneTwister(seed)

  # RWS-Diff authors suggest $10 <= d <= 20$.
  const dims = 30

  let angles = newSeqWith(dims, getMersenneFloat(mt))

  # https://en.wikipedia.org/wiki/N-sphere#Spherical_coordinates
  let firstRectCoord = cos(angles[0])
  let middle = map(toSeq(0..len(angles)-2),
                   proc(idx: int) : float =
                     result = foldl(angles[0..idx],
                                    a * sin(b), 1.0) * cos(angles[idx+1]))
  let lastRectCoord = foldl(angles, a*sin(b), 1.0)
  result = concat(@[firstRectCoord], middle, @[lastRectCoord])

  # Is this point actually on the unit $n$-sphere?
  doAssert isClose(foldl(result, a + b*b, 0.0), 1.0)

proc addVectors(a: FloatVec, b: FloatVec): FloatVec =
  doAssert len(a) == len(b)
  result = newSeq[float](len(a))
  for i in toSeq(0..len(a)-1):
    result[i] = a[i] + b[i]

proc distSqVectors(a: FloatVec, b: FloatVec): float =
  doAssert len(a) == len(b)
  result = 0.0
  for i in toSeq(0..len(a)-1):
    let diff = a[i] - b[i]
    result += diff*diff

# TODO: add more test cases, for this and other math routines
doAssert addVectors(@[1.0,2,3],@[4.0,6,8]) == @[5.0, 8.0, 11.0]

proc dotProduct(x: FloatVec, y: FloatVec): float =
  doAssert len(x) == len(y)
  let retval = foldl(zip(x, y), a + b[0]*b[1], 0.0)

proc cosineSimilarity(x: FloatVec, y: FloatVec): float =
  # Prefer unit vectors.
  # FIXME: this is ... not good ... numerics.
  let normX = sqrt(dotProduct(x, x))
  let normY = sqrt(dotProduct(y, y))
  if isClose(normX, 0) or isClose(normY, 0):
    result = 0.0
  else:
    result = foldl(zip(x, y), a + b[0]*b[1]/(normX*normY), 0.0)
  # TODO: assert in [-1, 1] since unit vecs

### Pseudo-module-boundary: RWS-Diff specific pq-grams
proc pqgramDfs(dirtree: FileInfoTree, q: int, ancestors: seq[string],
               prefix: string): (FloatVec, HashSet[(string, FloatVec)]) =
  # Slide over hash-sorted files at this node, $q$ at a time.
  let (dirs, files) = dirtree[prefix]
  let numFiles = len(files)
  let paddingLen = max(q - numFiles, 0)
  let paddedFiles = concat(files, newSeqWith(paddingLen,
                                              ("dummy", pathSep)))

  let pqgrams = map(toSeq(0..numFiles + paddingLen - q),
                    proc(idx: int): FloatVec =
                      let window = paddedFiles[idx..idx+q-1]
                      doAssert len(window) == q

                      # TODO: pick up renames elsewhere.
                      let pqgramHash = foldl(toMD5(foldl(ancestors, a & b) &
                                                    foldl(window, a & b[0],
                                                          ""))[0..3],
                                              a*256+b, 0'u32)
                      #echo ancestors, " ", window, " ", pqgramHash
                      result = genUnitSpherePoint(pqgramHash))

  # FIXME: Ugly kludge. Shouldn't specify dimensions except in one place.
  var sums = foldl(pqgrams, addVectors(a, b), newSeqWith(31, 0.0))
  var allSubTrees = initSet[(string, FloatVec)]()

  let foo = map(dirs,
                #proc(nextDir: string): (FloatVec, HashSet[(string, FloatVec)]) =
                proc(nextDir: string): FloatVec =
                  result = pqgramDfs(dirtree, q,
                                     concat(ancestors[1..^1], @[nextDir]),
                                     #prefix & nextDir & pathSep))
                                     prefix & nextDir & pathSep)[0])

  for nextDir in dirs:
    let (dir, rest) = pqgramDfs(dirtree, q,
                                concat(ancestors[1..^1], @[nextDir]),
                                prefix & nextDir & pathSep)

    # Record each subtree's information both separately and merged.
    # Track roots of children separately to avoid multiply counting.
    sums = addVectors(sums, dir)
    incl(allSubTrees, rest)
  incl(allSubTrees, (prefix, sums))
  result = (sums, allSubTrees)

proc createPQGrams(hashes: FileInfoBundleSet, p: int = 2,
                   q: int = 3) : Future[HashSet[(string, FloatVec)]] {.async.} =
  # RWS-Diff matches overlapping ancestor/children so thus facilitate
  # finding such pairs directly. This involves a few new assumptions,
  # such as paths having '/'-delineated structure and the distinction
  # between directories and files (the former are only ancestors, and
  # latter only leaves, in pq-grams, so there are $p$ directories and
  # $q$ files per pq-gram).

  # The number of ancesters (directories) per pq-gram
  doAssert p > 1

  # The number of adjacent children/leaves (files) per pq-gram
  doAssert q > 1

  # Initialize with $p$ dummy ancestors; pathSep harmless and can collapse
  # And then, starting from notional root pathSep, DFS through the tree.
  let (_, allSubTrees) = pqgramDfs(await createHashDirTree(hashes), q,
                                   newSeqWith(p, pathSep), pathSep)

  result = allSubTrees

proc generateEditScript() : void =
  discard


### Pseudo-module-boundary: overall driver
proc main(): Future[void] {.async.} =
  doAssert paramCount() >= 2
  let (hashes0Filtered, hashes1Filtered) = getFilteredHashes(paramStr(1),
                                                               paramStr(2))
  let subtrees1 = await createPQGrams(hashes0Filtered)
  let subtrees2 = await createPQGrams(hashes1Filtered)

  for item in items(subtrees1):
    for item2 in items(subtrees2):
      #let cs = cosineSimilarity(item[1], item2[1])
      let cs = distSqVectors(item[1], item2[1])
      if cs > 2:
        continue
      echo item[0], " ", item2[0], " ", cs

waitFor main()
