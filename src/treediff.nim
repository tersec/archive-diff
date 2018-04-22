#!/usr/bin/env nr

# Implements Finis, Jan P., et al. "Rws-diff: flexible and efficient change
# detection in hierarchical data." Proceedings of the 22nd ACM international
# conference on Information & Knowledge Management. ACM, 2013.
# https://db.in.tum.de/~finis/papers/RWS-Diff.pdf

import algorithm, asyncdispatch, asyncfile, md5, mersenne, math, os, re,
       sequtils, sets, strmisc, strutils, tables

const
  pathSep = "/"

type
  FloatVec = seq[float]
  FileInfoBundleTable = TableRef[string, seq[string]]
  FileInfoTree = TableRef[string, (HashSet[string], seq[(string, string)])]
  PQGramMap = HashSet[(string, FloatVec, int)]


### Pseudo-module-boundary: ingestion
proc readHashes(filename: string): Future[FileInfoBundleTable] {.async.} =
  let file = openAsync(filename)
  let data = await readAll(file)
  close(file)

  let splitLines = filter(map(split(data, "\n"), splitWhitespace),
                          proc(sl: auto): auto = len(sl) == 2)

  # For cases which
  # have multiple paths having duplicate hashes especially
  # across the two datasets being compared. Thus, keep all
  # paths with a given hash together to get O(1) checks.
  result = newTable[string, seq[string]]()
  for hashPath in splitLines:
    let hash = hashPath[0]

    if endswith(hashPath[1], pathSep) or endswith(hashPath[1], "\\"):
      # Only want leaf/file hashes. Construct rest.
      continue

    let path = @[hashPath[1]]
    if hash in result:
      insert(result[hash], path)
    else:
      result[hash] = path

## createHashPath and createHashDirTree modify same data structures;
## for refactoring purposes, they're coupled.
proc createHashPath(dirtree: auto, hash: auto, pathPrefix: auto,
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
    createHashPath(dirtree, hash, nextPath, pathElements[1 .. ^1])

proc sortHashTreeFiles(dirtree: auto): Future[void] {.async} =
  # This is why to put hash (or other similar properties) first in file-tuple.
  # It guarantees a useful sort order.
  for paths in keys(dirtree):
    dirtree[paths][1] = sorted(dirtree[paths][1], cmp)

proc createHashDirTree(hashes: auto): Future[FileInfoTree] {.async.} =
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
                                 proc(s: string): auto = len(s) > 1)

      createHashPath(result, hash, pathSep, pathElements)

  # Sort file but not directory entries; this removes spurious differences in
  # pq-grams, which matters increasingly with larger $q$.
  await sortHashTreeFiles(result)


### Pseudo-module-boundary: math
proc getMersenneFloat(m: var auto): auto =
  float(getNum(m))/float(high(uint32))*TAU

proc isClose(a: auto, b: auto): auto =
  # https://docs.scipy.org/doc/numpy/reference/generated/numpy.isclose.html
  abs(a - b) <= (1e-08 + 1e-05 * abs(b))

proc genUnitSpherePoint(seed: auto): auto =
  var mt = newMersenneTwister(seed)

  # RWS-Diff authors suggest $10 <= d <= 20$.
  const dims = 30

  let angles = newSeqWith(dims, getMersenneFloat(mt))

  # https://en.wikipedia.org/wiki/N-sphere#Spherical_coordinates
  result = concat(@[cos(angles[0])],
                  map(toSeq(0..len(angles)-2),
                    proc(idx: int): auto =
                      foldl(angles[0..idx],
                            a * sin(b), 1.0) * cos(angles[idx+1])),
                  @[foldl(angles, a*sin(b), 1.0)])

  # Is this point actually on the unit $n$-sphere?
  doAssert isClose(foldl(result, a + b*b, 0.0), 1.0)

proc addVectors(a: auto, b: auto): auto =
  doAssert len(a) == len(b)
  result = newSeq[float](len(a))
  for i in 0 .. len(a)-1:
    result[i] = a[i] + b[i]

proc distSqVectors(a: auto, b: auto): auto =
  doAssert len(a) == len(b)
  result = 0.0
  for i in 0 .. len(a)-1:
    let diff = a[i] - b[i]
    result += diff*diff

# TODO: add more test cases, for this and other math routines
doAssert addVectors(@[1.0,2,3], @[4.0,6,8]) == @[5.0, 8.0, 11.0]

proc whitenSeed(input: auto): auto =
  # PRNG seeds are u32, and input distributions may be uneven.
  foldl(toMD5(input)[0..3], a*256+b, 0'u32)

### Pseudo-module-boundary: RWS-Diff specific pq-grams
proc pqgramDfs(dirtree: auto, q: auto, ancestors: seq[string],
               prefix: auto): (FloatVec, PQGramMap) =
  # Slide over hash-sorted files at this node, $q$ at a time.
  let (dirs, files) = dirtree[prefix]
  let numFiles = len(files)
  let paddingLen = max(q - numFiles, 0)
  let paddedFiles = files & newSeqWith(paddingLen, ("dummy", pathSep))

  # FIXME: wrap around by $q-1$ siblings, and also use non-leaves in
  # pq-grams.
  # While it calculates on a file basis, it's for the directory.
  let pqgrams = map(toSeq(0..numFiles + paddingLen - q),
                    proc(idx: int): auto =
                      let window = paddedFiles[idx..idx+q-1]
                      doAssert len(window) == q

                      let pqgramHash = whitenSeed(foldl(ancestors, a & b) &
                                                  foldl(window, a & b[0], ""))
                      result = genUnitSpherePoint(pqgramHash))

  # FIXME: Shouldn't specify dimensions except in one place.
  var sums = foldl(pqgrams, addVectors(a, b), newSeqWith(31, 0.0))
  var allSubDirs = initSet[(string, FloatVec, int)]()

  let foo = map(dirs,
                proc(nextDir: string): auto =
                  pqgramDfs(dirtree, q,
                            ancestors[1 .. ^1] & @[nextDir],
                            #prefix & nextDir & pathSep))
                            prefix & nextDir & pathSep)[0])

  for nextDir in dirs:
    let (dir, rest) = pqgramDfs(dirtree, q, ancestors[1 .. ^1] & @[nextDir],
                                prefix & nextDir & pathSep)

    # Record each subtree's information both separately and merged.
    # Track childrens' roots separately to avoid multiply counting.
    sums = addVectors(sums, dir)
    incl(allSubDirs, rest)

  incl(allSubDirs, (prefix, sums, len(allSubDirs)))

  result = (sums, allSubDirs)

proc createPQGrams(hashes: auto, p: auto = 1, q: auto = 3):
                   Future[PQGramMap] {.async.} =
  # RWS-Diff matches overlapping ancestor/children so thus facilitate
  # finding such pairs directly. This involves a few new assumptions,
  # such as paths having '/'-delineated structure and the distinction
  # between directories and files; there are $p$ directories, and $q$
  # siblings, per pq-gram).

  # The number of ancesters (directories) per pq-gram
  doAssert p >= 1

  # The number of adjacent siblings (files and directories) per pq-gram
  doAssert q >= 1

  # Initialize with $p$ dummy ancestors; pathSep harmless and can collapse
  # And then, starting from notional root pathSep, DFS through the tree.
  let (_, dirs) = pqgramDfs(await createHashDirTree(hashes), q,
                            newSeqWith(p, pathSep), pathSep)

  result = dirs

proc isDirectory(path: auto): auto =
  endsWith(path, pathSep)

proc mapDirPQGrams(initialState: PQGramMap, goalState: PQGramMap):
                   TableRef[string, string] =
  # Use acceleration structures, e.g., k-d trees, to obtain O(n log n) at
  # a cost of approximating results; O(# dirs) per dir, or O(log(# dirs))
  # per dir.
  let initSubtrees = toSeq(items(initialState))

  # Ensure there is a closest-related-subtree.
  doAssert len(initSubtrees) >= 1

  # Multiple files (or multiple directories) might have similar pq-grams;
  # prefer similar filenames. (Almost) always match files with files, and
  # directories with directories.
  result = newTable[string, string]()
  for goalSubtree in items(goalState):
    # TODO: first check just for exact match

    # cmp compares with correct precedence.
    let dists = sorted(map(initSubtrees,
                           proc(initSubtree: auto): auto =
                             (distSqVectors(goalSubtree[1], initSubtree[1]),
                              editDistance(initSubtree[0], goalSubtree[0]),
                              initSubtree[0],
                              initSubtree[2])),
                       cmp)[0]

    # Scale allowed distance with potential distance.
    doAssert isDirectory(goalSubTree[0]) and isDirectory(dists[2])
    if float(dists[0])/(float(dists[3]+goalSubtree[2])) < 0.2:
      result[goalSubTree[0]] = dists[2]

proc mapFiles(initState: FileInfoBundleTable, goalState: FileInfoBundleTable):
              TableRef[string, string] =
  result = newTable[string, string]()
  for goalFiles in pairs(goalState):
    let (goalFileHash, goalPaths) = goalFiles
    if goalFileHash notin initState:
      continue
    let initPaths = initState[goalFileHash]
    for goalPath in goalPaths:
      if len(initPaths) == 1:
        # There's exactly one match. Don't waste time comparing paths; O(1)
        # fast/common path except in pathological scenarios.
        result[goalPath] = initPaths[0]
      else:
        # Attempt to reasonably handle duplicate files by matching files
        # with more similar paths and names in each hash set.
        let similarPath = sorted(map(initPaths,
                                     proc(initPath: auto): auto =
                                       (editDistance(goalPath, initPath),
                                        initPath)),
                                 cmp)[0][1]
        result[goalPath] = similarPath


### Pseudo-module-boundary: actual RWS-Diff algorithm
# TODO: for testing, pair operations w/ actual tree-building and encapsulate
proc generateInsertLeaf(): void =
  discard

proc generateCopy(): void =
  discard

proc generateMove(): void =
  discard

proc generateRename(): void =
  discard

proc generateDeleteLeaf(): void =
  discard

proc generateDeletions(initialPaths: seq[string],
                       pqgramMap: TableRef[string, string]): void =
  # Sufficient approximation of post-order traversal.
  let mappedInitSubtrees = toSet(toSeq(values(pqGramMap)))
  for initSubtree in sorted(initialPaths,
                            proc(x, y: auto): auto = -1*cmp(x, y)):
    if initSubtree notin mappedInitSubtrees:
        echo "deleteLeaf(\"" & initSubtree & "\")"

proc generateEditScript(initialPaths: seq[string], goalPaths: seq[string],
                        pqgramMap: TableRef[string, string]): auto =
  # Pre-order traversal to check parents before children,
  # but true pre-order depth-first search isn't necessary.
  var usedPrefixes = initSet[string]()

  for goalSubtree in sorted(goalPaths,
                            cmp):
    if goalSubtree notin pqgramMap:
        let destParent = "parent(\"" & goalSubtree & "\")"
        echo "insertLeaf(\"", goalSubtree, "\", ", destParent, ")"
        # update mapping initialState
    else:
      let initSubtree = pqGramMap[goalSubtree]
      # for m(parent), rpartition

      # Check if already used subtree; if so, must copy rather than move
      if initSubTree == goalSubTree and allIt(usedPrefixes, not startsWith(goalSubtree, it)):
        # echo "copy(\"", initSubTree, "\", M(parent(\"", goalSubtree, "\")"
        # update mapping initialState
        discard
      # FIXME: check parents
      elif initSubTree != goalSubTree:
        echo "mv(\"", initSubTree, "\", M(parent(\"", goalSubtree, "\")"

      incl(usedPrefixes, goalSubtree)

  generateDeletions(initialPaths, pqgramMap)

proc compareHashes(hashes0: auto, hashes1: auto): Future[void] {.async.} =
  # TODO: refactor toSeq(pairs(...))?
  let initDirs = await createPQGrams(toSet(toSeq(pairs(hashes0))))
  let goalDirs = await createPQGrams(toSet(toSeq(pairs(hashes1))))
  let merged = newTable(concat(toSeq(pairs(mapDirPQGrams(initDirs, goalDirs))),
                               toSeq(pairs(mapFiles(hashes0, hashes1)))))

  let emptyStrSeq: seq[string] = @[]
  let initPaths = concat(foldl(toSeq(values(hashes0)), a & b, emptyStrSeq),
                         map(toSeq(items(initDirs)),
                             proc(x: tuple[aa: string, bb: FloatVec, cc: int]): auto =
                               x[0]))

  let goalPaths = concat(foldl(toSeq(values(hashes1)), a & b, emptyStrSeq),
                         map(toSeq(items(goalDirs)),
                           proc(x: tuple[aa: string, bb: FloatVec, cc: int]): auto =
                             x[0]))

  generateEditScript(initPaths, goalPaths, merged)


### Pseudo-module-boundary: overall driver
proc main(): Future[void] {.async.} =
  doAssert paramCount() >= 2
  let hashes0 = await readHashes(paramStr(1))
  let hashes1 = await readHashes(paramStr(2))
  await compareHashes(hashes0, hashes1)

waitFor main()
