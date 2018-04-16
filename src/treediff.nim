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
  FileInfoBundle = (string, seq[string])
  FileInfoBundleTable = TableRef[string, seq[string]]
  FileInfoBundleSet = HashSet[FileInfoBundle]
  FileInfoTree = TableRef[string, (HashSet[string], seq[(string, string)])]
  PQGramMap = HashSet[(string, FloatVec, int)]


# FIXME: templatize more

### Pseudo-module-boundary: ingestion section
proc readHashes(filename: string): Future[FileInfoBundleTable]
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
    if hash in result:
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

proc sortHashTreeFiles(dirtree: FileInfoTree): Future[void] {.async} =
  # This is why to put hash (or other similar properties) first in file-tuple.
  # It guarantees a useful sort order.
  for paths in keys(dirtree):
    dirtree[paths][1] = sorted(dirtree[paths][1], cmp)

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
                                 proc(s: string): bool = len(s) > 1)

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
  const dims = 40

  let angles = newSeqWith(dims, getMersenneFloat(mt))

  # https://en.wikipedia.org/wiki/N-sphere#Spherical_coordinates
  let firstRectCoord = cos(angles[0])
  let middle = map(toSeq(0..len(angles)-2),
                   proc(idx: int): float =
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

### Pseudo-module-boundary: RWS-Diff specific pq-grams
proc pqgramDfs(dirtree: FileInfoTree, q: int, ancestors: seq[string],
               prefix: string): (FloatVec, PQGramMap) =
  # Slide over hash-sorted files at this node, $q$ at a time.
  let (dirs, files) = dirtree[prefix]
  let numFiles = len(files)
  let paddingLen = max(q - numFiles, 0)
  let paddedFiles = concat(files, newSeqWith(paddingLen,
                                              ("dummy", pathSep)))

  # FIXME: wrap around by $q-1$ siblings, and also use non-leaves in
  # pq-grams.
  # While it calculates on a file basis, it's all for the directory.
  let pqgrams = map(toSeq(0..numFiles + paddingLen - q),
                    proc(idx: int): FloatVec =
                      let window = paddedFiles[idx..idx+q-1]
                      doAssert len(window) == q

                      # TODO: Use this MD5 => u32 construction twice. refactor.
                      let pqgramHash = foldl(toMD5(foldl(ancestors, a & b) &
                                                   foldl(window, a & b[0],
                                                         ""))[0..3],
                                             a*256+b, 0'u32)
                      result = genUnitSpherePoint(pqgramHash))

  # FIXME: Shouldn't specify dimensions except in one place.
  var sums = foldl(pqgrams, addVectors(a, b), newSeqWith(41, 0.0))
  var allSubTrees = initSet[(string, FloatVec, int)]()

  let foo = map(dirs,
                #proc(nextDir: string): (FloatVec, PQGramMap) =
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

  # Special-case simple per-file calculations.
  # Correct way per "The pq-gram Distance between Ordered Labeled Trees" is
  # to have $q$ notional children of leaves of original tree, but since the
  # pqgram-hashing, etc is opaque and one-directional, it is unnecessary to
  # actually build out this notional tree. It just has to have distinct pq-
  # grams from the directories and be included hierarchically in the bags.
  for file in files:
    let (fileHash, fileName) = file
    incl(allSubTrees, (prefix & fileName,
                       genUnitSpherePoint(foldl(toMD5(fileHash)[0..3],
                                                a*256+b, 0'u32)),
                       1))

  incl(allSubTrees, (prefix, sums, len(allSubtrees)))

  result = (sums, allSubTrees)

proc createPQGrams(hashes: FileInfoBundleSet, p: int = 1,
                   q: int = 3): Future[PQGramMap] {.async.} =
  # RWS-Diff matches overlapping ancestor/children so thus facilitate
  # finding such pairs directly. This involves a few new assumptions,
  # such as paths having '/'-delineated structure and the distinction
  # between directories and files; there are $p$ directories, and $q$ siblings,
  # per pq-gram).

  # The number of ancesters (directories) per pq-gram
  doAssert p >= 1

  # The number of adjacent siblings (files and directories) per pq-gram
  doAssert q >= 1

  # Initialize with $p$ dummy ancestors; pathSep harmless and can collapse
  # And then, starting from notional root pathSep, DFS through the tree.
  let (_, allSubTrees) = pqgramDfs(await createHashDirTree(hashes), q,
                                   newSeqWith(p, pathSep), pathSep)

  result = allSubTrees

proc mapDestPQGrams(initialState: PQGramMap, goalState: PQGramMap) :
                   TableRef[string, string] =
  # In smaller cases, more exact O((# dirs)^2) brute-force algorithm. Can
  # use acceleration structures such as k-d trees to obtain O(n log n) at
  # a cost of approximating results; O(# dirs) per dir, or O(log(# dirs))
  # per dir.
  let initialSubtrees = toSeq(items(initialState))

  # Ensure there is a closest-related-subtree.
  doAssert len(initialSubtrees) >= 1

  # Multiple files (or multiple directories) might have similar pq-grams;
  # prefer similar filenames. (Almost) always match files with files, and
  # directories with directories.
  result = newTable[string, string]()
  for goalSubtree in items(goalState):
    # By setting up this way, cmp compares with correct precedence.
    # TODO: pull out isDirectory as utility function.
    let dists = sorted(map(initialSubtrees,
                           proc(initialSubtree: tuple[a: string, b: FloatVec, c: int]):
                                tuple[a: int, b: float, c: int, d: string, e: int] =
                             # TODO: for all these -- can just return expression?
                             result = (abs(int(endsWith(goalSubtree[0],
                                                        pathSep)) -
                                           int(endsWith(initialSubtree[0],
                                                        pathSep))),
                                       distSqVectors(goalSubtree[1],
                                                     initialSubtree[1]),
                                       editDistance(initialSubtree[0],
                                                    goalSubtree[0]),
                                       initialSubtree[0],
                                       initialSubtree[2])),
                       cmp)[0]

    # Files must match exactly, while directories can match approximately.
    # Scale allowed distance with potential distance.
    if ((not goalSubTree[0].endswith(pathSep) and isClose(dists[1], 0.0)) or
        (goalSubTree[0].endswith(pathSep) and
         float(dists[1])/(float(dists[4]+goalSubtree[2])) < 0.2)):
      result[goalSubTree[0]] = dists[3]

# FIXME: this is a general utility function and belongs elsewhere
proc reverseCmp[T](x, y: T): int =
  result = cmp(x, y) * -1

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

# TODO: extract extract-n'th-element
proc generateEditScript(initialState: PQGramMap, goalState: PQGramMap,
                        pqgramMap: TableRef[string, string]): void =
  # Pre-order traversal to check parents before children,
  # but true pre-order depth-first search isn't necessary.
  # echo pqgramMap

  var usedPrefixes = initSet[string]()

  for goalSubtree in sorted(map(toSeq(items(goalState)),
                                proc(x: tuple[a: string, b: FloatVec, c: int]):
                                     string = x[0]),
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

  # Sufficient approximation of post-order traversal.
  # FIXME: Separate enough to be a separate proc (generateDeletions),
  # depening on avoiding further data-structure coupling.
  let mappedInitSubtrees = toSet(toSeq(values(pqGramMap)))
  for initSubtree in sorted(map(toSeq(items(initialState)),
                                proc(x: tuple[a: string, b: FloatVec, c: int]): string =
                                  result = x[0]),
                            reverseCmp):
    if initSubtree notin mappedInitSubtrees:
        echo "deleteLeaf(\"" & initSubtree & "\")"

### Pseudo-module-boundary: overall driver
proc main(): Future[void] {.async.} =
  doAssert paramCount() >= 2
  # TODO: pull out for testability not depending on paramStr, etc,
  # so getFilteredHashes should take strings, read from files elsewhere.
  let (hashes0Filtered, hashes1Filtered) = getFilteredHashes(paramStr(1),
                                                             paramStr(2))
  let initialState = await createPQGrams(hashes0Filtered)
  let goalState = await createPQGrams(hashes1Filtered)

  generateEditScript(initialState, goalState,
                     mapDestPQGrams(initialState, goalState))

waitFor main()
