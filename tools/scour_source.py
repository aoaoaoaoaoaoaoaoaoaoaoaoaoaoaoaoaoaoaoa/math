#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///

"""Finite falsification of the Neary four-tile source equivalence.

This checker is intentionally independent of the Lean definitions. It exhausts arbitrary tile
words in small parameter regimes and separately reconstructs every bounded halting trace.
Finite success is not a proof; any failure is a counterexample or a transcription defect.
"""

from dataclasses import dataclass
from itertools import product
from typing import Final, Literal, assert_never

type Letter = Literal["b", "c"]
type Tile = Literal["Rc", "Rb", "Dc", "Db"]

LETTERS: Final[tuple[Letter, ...]] = ("b", "c")
TILES: Final[tuple[Tile, ...]] = ("Rc", "Rb", "Dc", "Db")


def encode(beta: int, word: tuple[Letter, ...]) -> str:
    return "".join("1" + "0" * beta + "1" if letter == "b" else "1" for letter in word)


@dataclass(frozen=True, slots=True)
class Instance:
    beta: int
    body: tuple[Letter, ...]

    @property
    def marker(self) -> str:
        return "1" + "0" * self.beta

    @property
    def initial(self) -> tuple[Letter, ...]:
        return self.body[self.beta - 1 :] + ("b",)

    def output(self, letter: Letter) -> tuple[Letter, ...]:
        match letter:
            case "b":
                return ("b",)
            case "c":
                return self.body + ("b",)
            case unreachable:
                assert_never(unreachable)

    def pair(self, tile: Tile) -> tuple[str, str]:
        hb = "1" + "0" * self.beta + "1"
        match tile:
            case "Rc":
                return "1", "1" + encode(self.beta, self.body) + "10"
            case "Rb":
                return hb, "110"
            case "Dc":
                return "1", "0"
            case "Db":
                return hb, "0"
            case unreachable:
                assert_never(unreachable)

    def terminal_match(self, word: tuple[Tile, ...]) -> bool:
        pairs = tuple(map(self.pair, word))
        return "".join(upper for upper, _ in pairs) + self.marker == "".join(
            lower for _, lower in pairs
        )

    def trace(self, limit: int) -> tuple[bool, tuple[tuple[Letter, ...], ...]]:
        queue = self.initial
        strokes: list[tuple[Letter, ...]] = []
        for _ in range(limit):
            if len(queue) < self.beta:
                return True, tuple(strokes)
            stroke = queue[: self.beta]
            strokes.append(stroke)
            queue = queue[self.beta :] + self.output(stroke[0])
        return len(queue) < self.beta, tuple(strokes)

    def witness(self, history: tuple[tuple[Letter, ...], ...]) -> tuple[Tile, ...]:
        initial_stroke = ("c",) + self.body[: self.beta - 1]
        strokes = (initial_stroke,) + history
        tiles: list[Tile] = []
        for stroke in strokes:
            assert len(stroke) == self.beta
            tiles.append("Rc" if stroke[0] == "c" else "Rb")
            tiles.extend("Dc" if letter == "c" else "Db" for letter in stroke[1:])
        return tuple(tiles)


def scour() -> None:
    arbitrary_words = 0
    terminal_matches = 0
    halting_witnesses = 0

    for beta, max_body, max_tiles in ((3, 4, 9), (4, 6, 8)):
        for body_length in range(beta - 1, max_body + 1):
            for body in product(LETTERS, repeat=body_length):
                instance = Instance(beta, body)

                for length in range(1, max_tiles + 1):
                    for word in product(TILES, repeat=length):
                        arbitrary_words += 1
                        if not instance.terminal_match(word):
                            continue
                        terminal_matches += 1
                        halted, _ = instance.trace(length // beta + 1)
                        if not halted:
                            raise AssertionError(
                                f"spurious terminal match: beta={beta}, body={body}, word={word}"
                            )

                if body_length % (beta - 1) != 0:
                    continue
                halted, history = instance.trace(12)
                if halted:
                    witness = instance.witness(history)
                    if not instance.terminal_match(witness):
                        raise AssertionError(
                            f"halting trace failed to match: beta={beta}, body={body}, "
                            f"history={history}, witness={witness}"
                        )
                    halting_witnesses += 1

    print(
        f"scoured {arbitrary_words:,} arbitrary tile words; "
        f"checked {terminal_matches:,} terminal matches and "
        f"{halting_witnesses:,} reconstructed halting witnesses"
    )


if __name__ == "__main__":
    scour()
