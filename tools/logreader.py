#!/usr/bin/python

import argparse
import json
import os
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, DefaultDict, List, Optional, Union


class ansi:
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    MAGENTA = '\033[95m'
    CYAN = '\033[96m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument('--file', help='Path to the log file', type=Path, default=Path('./log/checker'))
    parser.add_argument('--mode', help='Either `check` or `infer`', type=str, default='check')
    parser.add_argument('--name', help='Name of the function', type=str, default=None)
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    events_by_def_id_and_mode: DefaultDict[str,
                                           DefaultDict[str,
                                                       List[Any]]] = defaultdict(lambda: defaultdict(list))
    for line in open(args.file):
        event = json.loads(line)
        def_id = event['span']['def_id']
        mode = event['span']['name']
        events_by_def_id_and_mode[def_id][mode].append(event)

    buf = Buff()

    for def_id, modes in events_by_def_id_and_mode.items():
        if args.name is not None and args.name != def_id:
            continue

        for mode, events in modes.items():
            if args.mode != mode:
                continue
            buf.print(bold(f'{mode.upper()} {def_id}'))
            buf.print_rule('=')
            buf.print()
            buf.print_mode(events)
            buf.print('\n')

        buf.flush()


@dataclass
class Rule:
    c: str


class Buff:
    buffer: List[Union[str, Rule]]

    def __init__(self) -> None:
        self.buffer = []

    def flush(self) -> None:
        max_len = max(len(line) for line in self.buffer if isinstance(line, str))
        rule_len = min(max_len, os.get_terminal_size().columns)
        for line in self.buffer:
            if isinstance(line, Rule):
                print(line.c * rule_len)
            else:
                print(line)

        self.buffer = []

    def print(self, line: Union[str, Rule, None] = None) -> None:
        if line is None:
            line = ''
        self.buffer.append(line)

    def print_mode(self, events: List[dict]) -> None:
        for event in events:
            fields = event['fields']

            if fields['event'] == 'basic_block_start':
                self.print_bb_header(fields['bb'])
                self.print_context(fields['pcx'], fields['env'])
            elif fields['event'] == 'statement_end':
                if fields['stmt'] == 'nop':
                    continue
                self.print_stmt(fields['stmt'])
                self.print_context(fields['pcx'], fields['env'])
            elif fields['event'] == 'terminator_end':
                self.print_stmt(fields['terminator'])
                self.print_context(fields['pcx'], fields['env'])
                self.print_rule()
                self.print()

    def print_rule(self, c='-') -> None:
        self.print(Rule(c))

    def print_bb_header(self, bb: str) -> None:
        self.print(bold(bb))
        self.print_rule()

    def print_stmt(self, stmt: str) -> None:
        self.print(colorize(ansi.BLUE, stmt))

    def print_terminator(self, terminator: str) -> None:
        self.print(colorize(ansi.BLUE, terminator))

    def print_context(self, pcx: str, env: str) -> None:
        self.print(pcx)
        self.print(env)


def bold(text: str) -> str:
    return ansi.BOLD + text + ansi.ENDC


def colorize(color: str, text: str) -> str:
    return color + text + ansi.ENDC


if __name__ == "__main__":
    main()
