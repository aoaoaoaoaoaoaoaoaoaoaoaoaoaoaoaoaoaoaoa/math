#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///

"""Finite falsification of the Neary source and paired-role mortality compilers.

This checker is intentionally independent of the Lean definitions. It exhausts arbitrary tile
and compressed-control words in small parameter regimes, reconstructs bounded halting traces,
and multiplies the emitted `4 × 4` matrices directly. Finite success is not a proof; any failure
is a counterexample or a transcription defect.
"""

from dataclasses import dataclass
from itertools import product
from typing import Final, Literal, assert_never

type Letter = Literal["b", "c"]
type Tile = Literal["Rc", "Rb", "Dc", "Db"]
type Control = Literal["b", "c", "T"]
type MortalityLabel = Literal["b", "c", "T", "P"]
type Vector4 = tuple[int, int, int, int]
type Matrix4 = tuple[Vector4, Vector4, Vector4, Vector4]

LETTERS: Final[tuple[Letter, ...]] = ("b", "c")
TILES: Final[tuple[Tile, ...]] = ("Rc", "Rb", "Dc", "Db")
CONTROLS: Final[tuple[Control, ...]] = ("b", "c", "T")
MORTALITY_LABELS: Final[tuple[MortalityLabel, ...]] = ("b", "c", "T", "P")
IDENTITY4: Final[Matrix4] = (
    (1, 0, 0, 0),
    (0, 1, 0, 0),
    (0, 0, 1, 0),
    (0, 0, 0, 1),
)
ZERO4: Final[Matrix4] = (
    (0, 0, 0, 0),
    (0, 0, 0, 0),
    (0, 0, 0, 0),
    (0, 0, 0, 0),
)


def encode(beta: int, word: tuple[Letter, ...]) -> str:
    return "".join("1" + "0" * beta + "1" if letter == "b" else "1" for letter in word)


def ternary_code(bits: str) -> int:
    value = 0
    for bit in bits:
        value = 3 * value + (2 if bit == "1" else 1)
    return value


def matrix_mul(left: Matrix4, right: Matrix4) -> Matrix4:
    def row(i: int) -> Vector4:
        return (
            sum(left[i][k] * right[k][0] for k in range(4)),
            sum(left[i][k] * right[k][1] for k in range(4)),
            sum(left[i][k] * right[k][2] for k in range(4)),
            sum(left[i][k] * right[k][3] for k in range(4)),
        )

    return (row(0), row(1), row(2), row(3))


def matrix_product(matrices: tuple[Matrix4, ...]) -> Matrix4:
    result = IDENTITY4
    for matrix in matrices:
        result = matrix_mul(result, matrix)
    return result


def matrix_vector(matrix: Matrix4, vector: Vector4) -> Vector4:
    return (
        sum(matrix[0][j] * vector[j] for j in range(4)),
        sum(matrix[1][j] * vector[j] for j in range(4)),
        sum(matrix[2][j] * vector[j] for j in range(4)),
        sum(matrix[3][j] * vector[j] for j in range(4)),
    )


def outer(column: Vector4, row: Vector4) -> Matrix4:
    def scaled(i: int) -> Vector4:
        return (
            column[i] * row[0],
            column[i] * row[1],
            column[i] * row[2],
            column[i] * row[3],
        )

    return (scaled(0), scaled(1), scaled(2), scaled(3))


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

    @property
    def paired_column(self) -> Vector4:
        return (ternary_code(self.marker), -1, 3 ** len(self.marker), 0)

    def paired_data_matrix(self, letter: Letter) -> Matrix4:
        rule: Tile = "Rb" if letter == "b" else "Rc"
        erase: Tile = "Db" if letter == "b" else "Dc"
        upper, rule_lower = self.pair(rule)
        _, erase_lower = self.pair(erase)
        return (
            (
                1,
                ternary_code(rule_lower),
                ternary_code(upper),
                ternary_code(erase_lower),
            ),
            (0, 0, 0, 0),
            (0, 0, 3 ** len(upper), 0),
            (0, 3 ** len(rule_lower), 0, 3 ** len(erase_lower)),
        )

    def paired_generator(self, control: Control) -> Matrix4:
        match control:
            case "b" | "c":
                return self.paired_data_matrix(control)
            case "T":
                return (
                    (1, 0, 0, 0),
                    (0, 0, 0, 1),
                    (0, 0, 1, 0),
                    (0, 1, 0, 0),
                )
            case unreachable:
                assert_never(unreachable)

    def mortality_generator(self, label: MortalityLabel) -> Matrix4:
        match label:
            case "b" | "c" | "T":
                return self.paired_generator(label)
            case "P":
                return outer(self.paired_column, (1, 0, 0, 0))
            case unreachable:
                assert_never(unreachable)

    def decode_controls(self, word: tuple[Control, ...]) -> tuple[Tile, ...]:
        rule_phase = True
        decoded: list[Tile] = []
        for control in reversed(word):
            match control:
                case "T":
                    rule_phase = not rule_phase
                case "b":
                    decoded.append("Rb" if rule_phase else "Db")
                    rule_phase = False
                case "c":
                    decoded.append("Rc" if rule_phase else "Dc")
                    rule_phase = False
                case unreachable:
                    assert_never(unreachable)
        decoded.reverse()
        return tuple(decoded)

    def paired_coefficient(self, word: tuple[Control, ...]) -> int:
        product_matrix = matrix_product(tuple(map(self.paired_generator, word)))
        return matrix_vector(product_matrix, self.paired_column)[0]

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
    paired_coefficients = 0
    paired_mortality_products = 0

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

    paired_instances = (
        Instance(3, ("b", "b")),
        Instance(3, ("b", "c")),
        Instance(4, ("b", "c", "b")),
    )
    for instance in paired_instances:
        for control in CONTROLS:
            if tuple(row[0] for row in instance.paired_generator(control)) != (
                1,
                0,
                0,
                0,
            ):
                raise AssertionError(
                    f"control lost common first column: {instance=}, {control=}"
                )

        decoded_by_length: dict[int, set[tuple[Tile, ...]]] = {}
        for length in range(9):
            for word in product(CONTROLS, repeat=length):
                paired_coefficients += 1
                decoded = instance.decode_controls(word)
                decoded_by_length.setdefault(len(decoded), set()).add(decoded)
                upper = "".join(instance.pair(tile)[0] for tile in decoded)
                lower = "".join(instance.pair(tile)[1] for tile in decoded)
                expected = ternary_code(upper + instance.marker) - ternary_code(lower)
                actual = instance.paired_coefficient(word)
                if actual != expected:
                    raise AssertionError(
                        f"paired coefficient mismatch: {instance=}, {word=}, {decoded=}, "
                        f"{actual=}, {expected=}"
                    )

        for length in range(5):
            missing = set(product(TILES, repeat=length)) - decoded_by_length.get(
                length, set()
            )
            if missing:
                raise AssertionError(
                    f"bounded decoder not surjective: {instance=}, {length=}, "
                    f"first_missing={next(iter(missing))}"
                )

        for length in range(1, 8):
            for word in product(MORTALITY_LABELS, repeat=length):
                paired_mortality_products += 1
                actual_zero = (
                    matrix_product(tuple(map(instance.mortality_generator, word)))
                    == ZERO4
                )
                blocks: list[list[Control]] = [[]]
                for label in word:
                    if label == "P":
                        blocks.append([])
                    else:
                        blocks[-1].append(label)
                first_column_zero = matrix_vector(
                    matrix_product(tuple(map(instance.paired_generator, blocks[0]))),
                    instance.paired_column,
                ) == (0, 0, 0, 0)
                expected_zero = len(blocks) > 1 and (
                    first_column_zero
                    or any(
                        instance.paired_coefficient(tuple(block)) == 0
                        for block in blocks[1:-1]
                    )
                )
                if actual_zero != expected_zero:
                    raise AssertionError(
                        f"mortality fracture mismatch: {instance=}, {word=}, "
                        f"{actual_zero=}, {expected_zero=}"
                    )

    print(
        f"scoured {arbitrary_words:,} arbitrary tile words; "
        f"checked {terminal_matches:,} terminal matches and "
        f"{halting_witnesses:,} reconstructed halting witnesses; "
        f"checked {paired_coefficients:,} paired coefficients and "
        f"{paired_mortality_products:,} mortality products"
    )


if __name__ == "__main__":
    scour()
