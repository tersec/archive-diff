#!/usr/bin/env nr

# Implements Finis, Jan P., et al. "Rws-diff: flexible and efficient change
# detection in hierarchical data." Proceedings of the 22nd ACM international
# conference on Information & Knowledge Management. ACM, 2013.
# https://db.in.tum.de/~finis/papers/RWS-Diff.pdf

import algorithm, asyncdispatch, asyncfile, md5, mersenne, math, os, re,
       sequtils, sets, strutils, tables

const path_sep = "/"

### Pseudo-module-boundary: ingestion section
proc readHashes(filename: string) : Future[TableRef[string, seq[string]]]
     {.async.} =
  # Not truly asynchronous.
  let file = openAsync(filename)
  let data = await readAll(file)
  close(file)

  let split_lines = filter(map(split(data, "\n"), splitWhitespace),
                           proc(sl: seq[string]): bool = len(sl) == 2)

  # Start by filtering out identical paths, in common case
  # Allows for lower dimensionality for similar results in
  # later RWS-Diff stages. One nuance involves cases which
  # have multiple paths having duplicate hashes especially
  # across the two datasets being compared. Thus, keep all
  # paths with a given hash together.
  let hashes = newTable[string, seq[string]]()
  for hash_path in split_lines:
    let hash = hash_path[0]
    let path = @[hash_path[1]]
    if hasKey(hashes, hash):
      insert(hashes[hash], path)
    else:
      hashes[hash] = path

  return hashes

# FIXME typedef this, and a few other more complicated types
proc getFilteredHashes(filename1: string, filename2: string):
                      (HashSet[(string, seq[string])],
                       HashSet[(string, seq[string])]) =
  let pairs_h0 = toSet(toSeq(pairs(waitFor readHashes(filename1))))
  let pairs_h1 = toSet(toSeq(pairs(waitFor readHashes(filename2))))
  let pairs_common = pairs_h0 * pairs_h1

  # Ignore unchanged portions. Many tree diff algorithms are O(n^2)
  # or worse, so keep simple case quick, and ease debugging, with a
  # pair of large trees with relatively few differences.
  return (pairs_h0 - pairs_common, pairs_h1 - pairs_common)

## createHashPath and createHashDirTree modify same data structures;
## for refactoring purposes, they're coupled.
proc createHashPath(dirtree: TableRef[string, (HashSet[string],
                                               seq[(string, string)])],
                    hash: string, path_prefix: string,
                    path_elements: seq[string]): void =
  if len(path_elements) == 0:
    return
  elif len(path_elements) == 1:
    # Leaf node, file.
    insert(dirtree[path_prefix][1], (hash, path_elements[0]))
  else:
    doAssert len(path_elements) >= 2
    # Directory. Create if necessary, based on thus far built-up path.
    incl(dirTree[path_prefix][0], path_elements[0])
    let nextPath = path_prefix & path_elements[0] & path_sep
    if not hasKey(dirtree, nextPath):
      dirTree[nextPath] = (toSet[string]([]), @[])
    createHashPath(dirtree, hash, nextPath, path_elements[1..^1])

proc sortHashTreeFiles(dirtree: TableRef[string,
                                         (HashSet[string],
                                          seq[(string, string)])]):
                      Future[void] {.async} =
  # This is why to put hash (or other similar properties) first in file-tuple.
  # It guarantees a useful sort order.
  for paths in keys(dirtree):
    dirtree[paths][1] = sorted(dirtree[paths][1], system.cmp)

proc createHashDirTree(hashes: HashSet[(string, seq[string])]):
                      Future[TableRef[string, 
                                      (HashSet[string],
                                       seq[(string, string)])]] {.async.} =
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
  # FIXME: use distinct types for this.
  let dirtree = newTable[string, (HashSet[string], seq[(string, string)])]()
  dirtree[path_sep] = (toSet[string]([]), @[])

  for hash_paths in items(hashes):
    let (hash, paths) = hash_paths
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
      let path_elements = filter(split(replace(path, "^/+", ""), path_sep),
                                 proc(s: string) : bool = len(s) > 1)

      createHashPath(dirtree, hash, path_sep, path_elements)

  # Sort file but not directory entries; this removes spurious differences in
  # pq-grams, which matters increasingly with larger $q$.
  await sortHashTreeFiles(dirtree)
  return dirtree


### Pseudo-module-boundary: math section
proc getMersenneFloat(m: var MersenneTwister): float =
  return float(getNum(m))/float(high(uint32))*TAU

proc isClose(a: float, b: float): bool =
  # https://docs.scipy.org/doc/numpy/reference/generated/numpy.isclose.html
  const rtol = 1e-05
  const atol = 1e-08
  return abs(a - b) <= (atol + rtol * abs(b))

proc genUnitSphereCoord(seed: uint32): seq[float] =
  var mt = newMersenneTwister(seed)

  # RWS-Diff authors suggest $10 <= d <= 20$.
  const dims = 30

  let angles = newSeqWith(dims, getMersenneFloat(mt))

  # https://en.wikipedia.org/wiki/N-sphere#Spherical_coordinates
  let first_rect_coord = cos(angles[0])
  let middle = map(toSeq(0..len(angles)-2),
                   proc(idx: int) : float =
                     return foldl(angles[0..idx],
                                  a * sin(b), 1.0) * cos(angles[idx+1]))
  let last_rect_coord = foldl(angles, a*sin(b), 1.0)
  let rect_coords = concat(@[first_rect_coord], middle, @[last_rect_coord])

  # Is this point actually on the unit $n$-sphere?
  doAssert isClose(foldl(rect_coords, a + b*b, 0.0), 1.0)

  return rect_coords

proc add_vectors(a: seq[float], b: seq[float]): seq[float] =
  doAssert len(a) == len(b)
  var sum = newSeq[float](len(a))
  for i in toSeq(0..len(a)-1):
    sum[i] = a[i] + b[i]
  return sum

proc distsq_vectors(a: seq[float], b: seq[float]): float =
  doAssert len(a) == len(b)
  var sum = 0.0
  for i in toSeq(0..len(a)-1):
    let diff = a[i] - b[i]
    sum += diff*diff
  return sum

doAssert add_vectors(@[1.0,2,3],@[4.0,6,8]) == @[5.0, 8.0, 11.0]

proc dot_product(x: seq[float], y: seq[float]): float =
  doAssert len(x) == len(y)
  let retval = foldl(zip(x, y), a + b[0]*b[1], 0.0)

proc cosine_similarity(x: seq[float], y: seq[float]): float =
  # Prefer unit vectors.
  # FIXME: this is ... not good ... numerics.
  let norm_x = sqrt(dot_product(x, x))
  let norm_y = sqrt(dot_product(y, y))
  if isClose(norm_x, 0) or isClose(norm_y, 0):
    return 0.0
  let retval = foldl(zip(x, y), a + b[0]*b[1]/(norm_x*norm_y), 0.0)
  return retval

### Pseudo-module-boundary: RWS-Diff specific pq-grams
proc pqgramDfs(dirtree: TableRef[string, (HashSet[string],
                                          seq[(string, string)])],
               q: int, ancestors: seq[string], prefix: string):
               (seq[float], HashSet[(string, seq[float])]) =
  # Slide over hash-sorted files at this node, $q$ at a time.
  let (dirs, files) = dirtree[prefix]
  let num_files = len(files)
  let padding_len = max(q - num_files, 0)
  let padded_files = concat(files, newSeqWith(padding_len,
                                              ("dummy", path_sep)))

  let pqgrams = map(toSeq(0..num_files + padding_len - q),
                    proc(idx: int): seq[float] =
                      let window = padded_files[idx..idx+q-1]
                      doAssert len(window) == q

                      # For $d$-dimensional sphere for RWD. Use hashes only.
                      # TODO: ... pick up renames elsewhere.
                      let pqgram_hash = foldl(toMD5(foldl(ancestors, a & b) &
                                                    foldl(window, a & b[0],
                                                          ""))[0..3],
                                              a*256+b, 0'u32)
                      #echo ancestors, " ", window, " ", pqgram_hash
                      return genUnitSphereCoord(pqgram_hash))

  # FIXME: Ugly kludge. Shouldn't specify dimensions except in one place.
  var sums = foldl(pqgrams, add_vectors(a, b), newSeqWith(31, 0.0))
  var allSubTrees = initSet[(string, seq[float])]()

  for nextDir in dirs:
    let (dir, rest) = pqgramDfs(dirtree, q,
                                concat(ancestors[1..^1], @[nextDir]),
                                prefix & nextDir & path_sep)

    # Record each subtree's information both separately and merged.
    # Track roots of children separately to avoid multiply counting.
    sums = add_vectors(sums, dir)
    incl(allSubTrees, rest)
  incl(allSubTrees, (prefix, sums))
  return (sums, allSubTrees)

proc createPQGrams(hashes: HashSet[(string, seq[string])], p: int = 2,
                   q: int = 2) : Future[HashSet[(string, seq[float])]] {.async.} =
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

  # Initialize with $p$ dummy ancestors; path_sep harmless and can collapse later
  # And then, starting from notional root path_sep, DFS through the tree.
  let (_, allSubTrees) = pqgramDfs(await createHashDirTree(hashes), q,
                                   newSeqWith(p, path_sep), path_sep)

  return allSubTrees

proc calcDirWalks() : void =
  # in particular -- choose best of $l$ NNs (fixed $l$i). based on L_2 metric.
  # okay for now just use literal hash (numeric function thereof). obv date soon
  discard

### Pseudo-module-boundary: overall driver
proc main(): Future[void] {.async.}=
  doAssert paramCount() >= 2
  let (hashes0_filtered, hashes1_filtered) = getFilteredHashes(paramStr(1),
                                                               paramStr(2))
  let subtrees1 = await createPQGrams(hashes0_filtered)
  let subtrees2 = await createPQGrams(hashes1_filtered)

  for item in items(subtrees1):
    for item2 in items(subtrees2):
      #let cs = cosine_similarity(item[1], item2[1])
      let cs = distsq_vectors(item[1], item2[1])
      if cs > 2:
        continue
      echo item[0], " ", item2[0], " ", cs

waitFor main()
