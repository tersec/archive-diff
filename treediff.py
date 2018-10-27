#!/usr/bin/env python3

from collections import namedtuple

Action = namedtuple("Action", ("type", "args"))


def parse_hashes(hash_list):
    for hash_, s in sorted(
        (_.split("  ", 1) for _ in open(hash_list, "r").read().strip().split("\n"))
    ):
        # These paths need to be hashable.
        yield hash_, tuple(s.split("/"))


def load_hashes(hash_list):
    from itertools import groupby
    from operator import itemgetter

    return {
        hash_: frozenset(map(itemgetter(1), hashes_paths))
        for hash_, hashes_paths in groupby(parse_hashes(hash_list), itemgetter(0))
    }


def find_common_copies(src, dst, active_targets):
    from collections import Counter
    from operator import itemgetter

    counter = Counter()
    remove_targets = set()
    for shared_hash in active_targets:
        src_paths = src[shared_hash]
        dst_paths = dst[shared_hash] - src_paths

        if len(dst_paths) == 0:
            # Don't keep searching every time. That hash is done.
            remove_targets.add(shared_hash)

        for dst_path in dst_paths:
            # Allows addressing last element (filename)
            dst_path_len = len(dst_path)

            for src_path in src_paths:
                src_path_len = len(src_path)

                for path_chunk_size in range(min(dst_path_len, src_path_len)):
                    copy_from, copy_to = (
                        src_path[: src_path_len - path_chunk_size],
                        dst_path[: dst_path_len - path_chunk_size],
                    )
                    if copy_from == copy_to:
                        continue

                    # Don't allow copying from parent to child; semi-artificial constraint
                    if (
                        src_path_len <= dst_path_len
                        and copy_from == copy_to[: len(copy_from)]
                    ):
                        break

                    # Found divergent path element; copying parent pointless
                    if (
                        src_path[src_path_len - path_chunk_size :]
                        != dst_path[dst_path_len - path_chunk_size :]
                    ):
                        break

                    counter[(copy_from, copy_to)] += 1

    return (
        tuple(map(itemgetter(0), counter.most_common(None))),
        active_targets - remove_targets,
    )


def get_compatible_concurrent_copies(copy_paths):
    # find_common_copies is expensive, so call it as little as possible.
    from itertools import product

    allowed_copies = []

    # This assumes most_common ordering.
    for copy_from, copy_to in copy_paths:
        if any(
            (
                any(
                    (
                        path0 == path1[: len(path0)] or path1 == path0[: len(path1)]
                        for path0, path1 in product(
                            (copy_from, copy_to), (allowed_copy_from, allowed_copy_to)
                        )
                    )
                )
                for allowed_copy_from, allowed_copy_to in allowed_copies
            )
        ):
            continue
        allowed_copies.append((copy_from, copy_to))

    return allowed_copies


def build_copy_matcher(copies):
    from bisect import bisect
    from operator import itemgetter

    replacement_table = dict(copies)
    search_table = sorted(map(itemgetter(0), copies))

    def matcher(path):
        position = bisect(search_table, path) - 1
        if position < 0:
            return path

        tentative_match = search_table[position]
        if tentative_match == path[: len(tentative_match)]:
            return replacement_table[tentative_match] + path[len(tentative_match) :]
        return path

    return matcher


def copy_(old_hashlist, copies):
    matcher = build_copy_matcher(copies)

    return (
        {
            hash_: frozenset(map(matcher, paths)) | paths
            for hash_, paths in old_hashlist.items()
        },
        # TODO: in principle one could distinguish between directory/file copies
        tuple((Action("cp_r", (src, dst)) for src, dst in copies)),
    )


def render_action(action):
    from os.path import sep

    return (action[0],) + tuple(map(sep.join, action[1]))


def get_hashlist_paths(hashlist):
    from itertools import chain

    return frozenset(chain.from_iterable(hashlist.values()))


def get_hashlist_path_prefixes(hashlist):
    from itertools import chain

    return frozenset(
        chain.from_iterable(
            (
                (tuple(path[:i]) for i in range(len(path)))
                for path in get_hashlist_paths(hashlist)
            )
        )
    )


def delete_by_path(hashlist_0, hashlist_1):
    from operator import attrgetter

    final_paths = get_hashlist_paths(hashlist_1)
    final_path_prefixes = get_hashlist_path_prefixes(hashlist_1)

    # This contains intermediate path prefixes, subsumed by parents' removal.
    removed_dirs = get_hashlist_path_prefixes(hashlist_0) - final_path_prefixes

    # But since directory removal is recursive, only have to get topmost parent.
    dir_removal_actions = tuple(
        [
            Action("rm_r", (removed_dir,))
            for removed_dir in removed_dirs
            if removed_dir[:-1] not in removed_dirs
        ]
    )

    empty = frozenset()
    file_removal_actions = []

    for hash_, paths in hashlist_0.items():
        for path in paths - hashlist_1.get(hash_, empty):
            if path in final_paths:
                # FIXME: for reconstruction from steps to be able to include this,
                # need to be able to query path's hash in final, i.e.
                # final_paths (and thus get_hashlist_paths) needs to return more
                # annotated information. It's convenient as a frozenset, so want some
                # data struxture allowing comparable operations easily.
                # basically, add/subtract. but define desired semantics.
                file_removal_actions.append(Action("modify", (path,)))
            elif path[:-1] not in removed_dirs:
                file_removal_actions.append(Action("rm", (path,)))

    assert (
        len(
            frozenset(map(attrgetter("args"), dir_removal_actions))
            & frozenset(map(attrgetter("args"), file_removal_actions))
        )
        == 0
    )

    return (
        {
            _: __
            for _, __ in (
                (hash_, frozenset(paths) & hashlist_1.get(hash_, empty))
                for hash_, paths in hashlist_0.items()
            )
            if len(__) > 0
        },
        dir_removal_actions + tuple(file_removal_actions),
    )


def validate_result(old_hashlist, new_hashlist):
    old_hashes = frozenset(old_hashlist.keys())
    new_hashes = frozenset(new_hashlist.keys())
    added_hashes = new_hashes - old_hashes
    assert {hash_: paths for hash_, paths in old_hashlist.items()} == {
        k: v for k, v in new_hashlist.items() if k not in added_hashes
    }


def treediff_copy(old_hashlist, new_hashlist):
    active_search_keys = frozenset(old_hashlist.keys()) & frozenset(new_hashlist.keys())
    copy_and_move_actions = ()
    while True:
        common_copies, active_search_keys = find_common_copies(
            old_hashlist, new_hashlist, active_search_keys
        )
        if len(common_copies) == 0:
            break
        working_copies = get_compatible_concurrent_copies(common_copies)
        old_hashlist, copy_actions_sub = copy_(old_hashlist, working_copies)
        copy_and_move_actions = copy_and_move_actions + copy_actions_sub

    return old_hashlist, copy_and_move_actions


def convert_copy_delete_to_move(copy_and_move_actions, deletion_actions):
    from operator import attrgetter, itemgetter

    deleted_dirs = frozenset(
        map(itemgetter(0), map(attrgetter("args"), deletion_actions))
    )
    mv_paths = set()

    # Can only convert last cp_r to mv each time, so run in reverse order, then
    # re-reverse copy actions later.
    copy_actions = []
    move_actions = []
    for copy_or_move_action in reversed(copy_and_move_actions):
        src = copy_or_move_action.args[0]
        if src in deleted_dirs and src not in mv_paths:
            mv_paths.add(deleted_dirs)
            move_actions.append(Action("mv", copy_or_move_action.args))
        else:
            copy_actions.append(Action("cp_r", copy_or_move_action.args))

    # Not sure if move_actions needs reversal.
    return tuple(reversed(copy_actions)), tuple(reversed(move_actions)), mv_paths


def treediff(old_hashlist, new_hashlist):
    old_hashlist, copy_and_move_actions = treediff_copy(old_hashlist, new_hashlist)
    old_hashlist, deletion_actions = delete_by_path(old_hashlist, new_hashlist)
    validate_result(old_hashlist, new_hashlist)

    copy_actions, move_actions, mv_paths = convert_copy_delete_to_move(
        copy_and_move_actions, deletion_actions
    )

    # Less important for archive verification. Necesary for completeness.
    creation_actions = tuple(
        (
            Action("create", (created_path,))
            for created_path in get_hashlist_paths(new_hashlist)
            - get_hashlist_paths(old_hashlist)
        )
    )

    # Skips creation_actions, since basically uninteresting.
    return (
        copy_actions
        + move_actions
        + tuple(
            (action for action in deletion_actions if action.args[0] not in mv_paths)
        )
    )


def action_transform(hashes, action):
    if action.type == "cp_r":
        result, _ = copy_(hashes, (action.args,))
        return result
    elif action.type == "rm" or action.type == "rm_r":
        # TODO: could more tightly assert here by distinguishing between rm and rm_r
        return
    elif action.type == "mv":
        return action_transform(
            action_transform(hashes, Action("cp_r", action.args)),
            Action("rm_r", action.args),
        )
    assert False


def treediff_replay(hashes, actions):
    # Verify that the edit script works.
    # render_action(action)
    for action in actions:
        hashes = action_transform(hashes, action)
    return hashes


def main():
    from sys import argv
    from pprint import pprint

    old_hashes, new_hashes = (load_hashes(argv[1]), load_hashes(argv[2]))
    actions = treediff(old_hashes, new_hashes)
    pprint(actions)
    assert treediff_replay(old_hashes, actions) == new_hashes


if __name__ == "__main__":
    main()
