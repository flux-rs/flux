#!/usr/bin/python

import argparse
import json
import os
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, DefaultDict, List, Optional, Union, Dict


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
    parser.add_argument('--filter', help='Events to filter', type=str, action='append')
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    events_by_def_id_and_mode: DefaultDict[str,
                                           DefaultDict[str,
                                                       List[Any]]] = defaultdict(lambda: defaultdict(list))
    bb_envs_infer: Dict[str, Any] = {}
    for line in open(args.file):
        event = json.loads(line)
        def_id = event['span']['def_id']
        mode = event['span']['name']
        events_by_def_id_and_mode[def_id][mode].append(event)
        if bb_envs_infer.get(def_id) is None:
            bb_envs_infer[def_id] = event['span'].get('bb_envs_infer')

    buf = Buff()

    for def_id, modes in events_by_def_id_and_mode.items():
        if args.name is not None and args.name not in def_id:
            continue

        for mode, events in modes.items():
            if args.mode != mode:
                continue
            buf.print(bold(f'{mode.upper()} {def_id}'))
            if args.mode == "check" and bb_envs_infer[def_id] is not None:
                buf.print(bb_envs_infer[def_id])
            buf.print_rule('═')
            buf.print()
            buf.print_mode(events, args.filter)
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
        max_len = max((len(line) for line in self.buffer if isinstance(line, str)), default=0)
        try:
            rule_len = min(max_len, os.get_terminal_size().columns)
        except OSError:
            rule_len = max_len
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

    def print_mode(self, events: List[dict], filters: Optional[List[str]]) -> None:
        for event in events:
            fields = event['fields']

            if filters is not None and fields['event'] not in filters:
                continue

            if fields['event'] == 'basic_block_start':
                self.flush()
                self.print()
                self.print_bb_header(fields['bb'])
                self.print_context(fields['rcx'], fields['env'])
            elif fields['event'] == 'statement_start':
                if fields['stmt'] == 'nop':
                    continue
                self.print_stmt(fields['stmt'])
            elif fields['event'] == 'statement_end':
                if fields['stmt'] == 'nop':
                    continue
                self.print_context(fields['rcx'], fields['env'])
            elif fields['event'] == 'terminator_start':
                self.print_terminator(fields['terminator'])
            elif fields['event'] == 'terminator_end':
                self.print_context(fields['rcx'], fields['env'])
                self.print_rule()
            elif fields['event'] == 'check_goto':
                self.print(f'goto {fields["target"]}')
                self.print_context(fields['rcx'], fields['env'])
                self.print('==>')
                self.print(fields['bb_env'])
                self.print_rule()
            elif fields['event'] == 'infer_goto_enter':
                self.print(f'goto {fields["target"]}')
                # self.print(fields['scope'])
                self.print(fields['bb_env'])
                self.print("⊓")
                self.print(fields['env'])
            elif fields['event'] == 'infer_goto_exit':
                self.print("=")
                self.print(fields['bb_env'])
                self.print_rule()

    def print_rule(self, c='─') -> None:
        self.print(Rule(c))

    def print_bb_header(self, bb: str) -> None:
        self.print(bold(bb))
        self.print_rule()

    def print_stmt(self, stmt: str) -> None:
        self.print(colorize(ansi.BLUE, stmt))

    def print_terminator(self, terminator: str) -> None:
        self.print(colorize(ansi.MAGENTA, terminator))

    def print_context(self, rcx: str, env: str) -> None:
        self.print(rcx)
        self.print(env)


def bold(text: str) -> str:
    return ansi.BOLD + text + ansi.ENDC


def colorize(color: str, text: str) -> str:
    return color + text + ansi.ENDC


if __name__ == "__main__":
    main()
