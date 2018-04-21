#!/usr/bin/env nr

# Implements Finis, Jan P., et al. "Rws-diff: flexible and efficient change
# detection in hierarchical data." Proceedings of the 22nd ACM international
# conference on Information & Knowledge Management. ACM, 2013.
# https://db.in.tum.de/~finis/papers/RWS-Diff.pdf

import algorithm, asyncdispatch, asyncfile, md5, mersenne, math, os, re,
       sequtils, sets, strmisc, strutils, tables

const pathSep = "/"

type
  FloatVec = seq[float]
  FileInfoBundleTable = TableRef[string, seq[string]]
  FileInfoTree = TableRef[string, (HashSet[string], seq[(string, string)])]
  PQGramMap = HashSet[(string, FloatVec, int)]


### Pseudo-module-boundary: ingestion
proc readHashes(filename: string): Future[FileInfoBundleTable] {.async.} =
  # Not truly asynchronous.
  let file = openAsync(filename)
  let data = await readAll(file)
  close(file)

  let splitLines = filter(map(split(data, "\n"), splitWhitespace),
                           proc(sl: auto): auto = len(sl) == 2)

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
    if hash in result:
      insert(result[hash], path)
    else:
      result[hash] = path

proc getFilteredHashes(hashes0: auto, hashes1: auto): auto =
  let pairsH0 = toSet(toSeq(pairs(hashes0)))
  let pairsH1 = toSet(toSeq(pairs(hashes1)))
  let pairsCommon = pairsH0 * pairsH1

  # Ignore unchanged portions. Many tree diff algorithms are O(n^2)
  # or worse, so keep pairs of large trees with few changes fast.
  result = (pairsH0 - pairsCommon, pairsH1 - pairsCommon)

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
  const rtol = 1e-05
  const atol = 1e-08
  result = abs(a - b) <= (atol + rtol * abs(b))

proc genUnitSpherePoint(seed: auto): auto =
  var mt = newMersenneTwister(seed)

  # RWS-Diff authors suggest $10 <= d <= 20$.
  const dims = 30

  let angles = newSeqWith(dims, getMersenneFloat(mt))

  # https://en.wikipedia.org/wiki/N-sphere#Spherical_coordinates
  let firstRectCoord = cos(angles[0])
  let middle = map(toSeq(0..len(angles)-2),
                   proc(idx: int): auto =
                     foldl(angles[0..idx],
                           a * sin(b), 1.0) * cos(angles[idx+1]))
  let lastRectCoord = foldl(angles, a*sin(b), 1.0)
  result = concat(@[firstRectCoord], middle, @[lastRectCoord])

  # Is this point actually on the unit $n$-sphere?
  doAssert isClose(foldl(result, a + b*b, 0.0), 1.0)

proc addVectors(a: auto, b: auto): auto =
  doAssert len(a) == len(b)
  result = newSeq[float](len(a))
  for i in toSeq(0..len(a)-1):
    result[i] = a[i] + b[i]

proc distSqVectors(a: auto, b: auto): auto =
  doAssert len(a) == len(b)
  result = 0.0
  for i in toSeq(0..len(a)-1):
    let diff = a[i] - b[i]
    result += diff*diff

# TODO: add more test cases, for this and other math routines
doAssert addVectors(@[1.0,2,3],@[4.0,6,8]) == @[5.0, 8.0, 11.0]

proc whitenSeed(input: auto): auto =
  # PRNG seeds are u32, and input distributions may be uneven.
  foldl(toMD5(input)[0..3], a*256+b, 0'u32)

### Pseudo-module-boundary: RWS-Diff specific pq-grams
proc pqgramDfs(dirtree: auto, q: auto, ancestors: seq[string],
               prefix: auto): (FloatVec, PQGramMap, PQGramMap) =
  # Slide over hash-sorted files at this node, $q$ at a time.
  let (dirs, files) = dirtree[prefix]
  let numFiles = len(files)
  let paddingLen = max(q - numFiles, 0)
  let paddedFiles = concat(files, newSeqWith(paddingLen,
                                             ("dummy", pathSep)))

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
  var allSubFiles = initSet[(string, FloatVec, int)]()

  let foo = map(dirs,
                proc(nextDir: string): auto =
                  pqgramDfs(dirtree, q,
                            concat(ancestors[1 .. ^1], @[nextDir]),
                            #prefix & nextDir & pathSep))
                            prefix & nextDir & pathSep)[0])

  for nextDir in dirs:
    let (dir, restDir, restFiles) = pqgramDfs(dirtree, q,
                                              concat(ancestors[1 .. ^1],
                                                     @[nextDir]),
                                              prefix & nextDir & pathSep)

    # Record each subtree's information both separately and merged.
    # Track roots of children separately to avoid multiply counting.
    sums = addVectors(sums, dir)
    incl(allSubDirs, restDir)
    incl(allSubFiles, restFiles)

  # Special-case simple per-file calculations.
  # Correct way per "The pq-gram Distance between Ordered Labeled Trees" is
  # to have $q$ notional children of leaves of original tree, but since the
  # pqgram-hashing, etc is opaque and one-directional, it is unnecessary to
  # actually build out this notional tree. It just has to have distinct pq-
  # grams from the directories and be included hierarchically in the bags.
  for file in files:
    let (fileHash, fileName) = file
    incl(allSubFiles, (prefix & fileName,
                       genUnitSpherePoint(whitenSeed(fileHash)), 1))

  incl(allSubDirs, (prefix, sums, len(allSubDirs)))

  result = (sums, allSubDirs, allSubFiles)

proc createPQGrams(hashes: auto, p: auto = 1, q: auto = 3):
                  Future[(PQGramMap, PQGramMap)] {.async.} =
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
  let (_, dirs, files) = pqgramDfs(await createHashDirTree(hashes), q,
                                   newSeqWith(p, pathSep), pathSep)

  result = (dirs, files)

proc isDirectory(path: auto): auto =
  endsWith(path, pathSep)

proc mapDestPQGrams(initialState: PQGramMap, goalState: PQGramMap) :
                   TableRef[string, string] =
  # In smaller cases, more exact O((# dirs)^2) brute-force algorithm. Can
  # use acceleration structures such as k-d trees to obtain O(n log n) at
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
    # cmp compares with correct precedence.
    let dists = sorted(map(initSubtrees,
                           proc(initSubtree: auto): auto =
                             (distSqVectors(goalSubtree[1], initSubtree[1]),
                              editDistance(initSubtree[0], goalSubtree[0]),
                              initSubtree[0],
                              initSubtree[2])),
                       cmp)[0]

    # Files must match exactly, while directories can match approximately.
    # Scale allowed distance with potential distance.
    doAssert isDirectory(goalSubTree[0]) == isDirectory(dists[2])
    if (not isDirectory(goalSubTree[0]) and isClose(dists[0], 0.0)) or
       (isDirectory(goalSubTree[0]) and
        float(dists[0])/(float(dists[3]+goalSubtree[2])) < 0.2):
      result[goalSubTree[0]] = dists[2]

## Substantial section
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

proc generateDeletions(initialState: PQGramMap,
                       pqgramMap: TableRef[string, string]): void =
  # Sufficient approximation of post-order traversal.
  let mappedInitSubtrees = toSet(toSeq(values(pqGramMap)))
  for initSubtree in sorted(map(toSeq(items(initialState)),
                                proc(x: auto): auto = x[0]),
                            proc(x, y: auto): auto = -1*cmp(x, y)):
    if initSubtree notin mappedInitSubtrees:
        echo "deleteLeaf(\"" & initSubtree & "\")"

proc generateEditScript(initialState: PQGramMap, goalState: PQGramMap,
                        pqgramMap: TableRef[string, string]): auto =
  # Pre-order traversal to check parents before children,
  # but true pre-order depth-first search isn't necessary.
  var usedPrefixes = initSet[string]()

  for goalSubtree in sorted(map(toSeq(items(goalState)),
                                proc(x: auto): auto = x[0]),
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
        echo "copy(\"", initSubTree, "\", M(parent(\"", goalSubtree, "\")"
        # update mapping initialState
      # FIXME: check parents
      elif initSubTree != goalSubTree:
        echo "mv(\"", initSubTree, "\", M(parent(\"", goalSubtree, "\")"

      incl(usedPrefixes, goalSubtree)

  generateDeletions(initialState, pqgramMap)

proc compareHashes(hashes0: auto, hashes1: auto): Future[void] {.async.} =
  let (hashes0Filtered, hashes1Filtered) = getFilteredHashes(hashes0, hashes1)
  let (initialDirs, initialFiles) = await createPQGrams(hashes0Filtered)
  let (goalDirs, goalFiles) = await createPQGrams(hashes1Filtered)

  let dirMap = mapDestPQGrams(initialDirs, goalDirs)
  let fileMap = mapDestPQGrams(initialFiles, goalFiles)
  let merged = newTable(concat(toSeq(pairs(dirMap)), toSeq(pairs(fileMap))))
  let initialState = toSet(concat(toSeq(items(initialDirs)),
                                  toSeq(items(initialFiles))))
  let goalState = toSet(concat(toSeq(items(goalDirs)),
                               toSeq(items(goalFiles))))

  generateEditScript(initialState, goalState, merged)


### Pseudo-module-boundary: overall driver
proc main(): Future[void] {.async.} =
  doAssert paramCount() >= 2
  let hashes0 = await readHashes(paramStr(1))
  let hashes1 = await readHashes(paramStr(2))
  await compareHashes(hashes0, hashes1)

waitFor main()
