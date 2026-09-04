#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///

from __future__ import annotations

import argparse
import html
import json
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Never, TypeVar, assert_never, cast


class NodeKind(StrEnum):
    DEFINITION = "definition"
    CONSTRUCTION = "construction"
    LEMMA = "lemma"
    REDUCTION = "reduction"
    THEOREM = "theorem"
    OBSTRUCTION = "obstruction"
    WITNESS = "witness"


class Prominence(StrEnum):
    SUPPORTING = "supporting"
    LOAD_BEARING = "load-bearing"
    ENDPOINT = "endpoint"


class Origin(StrEnum):
    LITERATURE = "literature"
    PROJECT = "project"
    MIXED = "mixed"


class Assurance(StrEnum):
    FORMALIZED = "formalized"
    AUDITED = "audited"
    COMPUTATIONAL = "computational"
    REPORTED = "reported"


class RelationKind(StrEnum):
    SPECIALIZES = "specializes"
    INSTANTIATES = "instantiates"
    STRENGTHENS = "strengthens"
    TRANSPORTS = "transports"
    DISPUTES = "disputes"


@dataclass(frozen=True, slots=True)
class Relation:
    kind: RelationKind
    target: str


@dataclass(frozen=True, slots=True)
class Node:
    id: str
    kind: NodeKind
    prominence: Prominence
    origin: Origin
    assurance: Assurance
    title: str
    summary: str
    href: str
    requires: tuple[str, ...]
    relations: tuple[Relation, ...]


@dataclass(frozen=True, slots=True)
class View:
    id: str
    title: str
    summary: str
    nodes: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class Graph:
    collection: str
    nodes: tuple[Node, ...]
    views: tuple[View, ...]


EnumT = TypeVar("EnumT", bound=StrEnum)
ID_PATTERN = re.compile(r"^mm/[a-z0-9]+(?:-[a-z0-9]+)*$")
VIEW_PATTERN = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
TOC_BEGIN = "<!-- MODULE_GRAPH_TOC:BEGIN -->"
TOC_END = "<!-- MODULE_GRAPH_TOC:END -->"
GRAPH_BEGIN = "<!-- MODULE_GRAPH:BEGIN -->"
GRAPH_END = "<!-- MODULE_GRAPH:END -->"


def fail(message: str) -> Never:
    raise ValueError(message)


def as_object(value: object, context: str) -> dict[str, object]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        fail(f"{context} must be an object with string keys")
    return cast(dict[str, object], value)


def as_list(value: object, context: str) -> list[object]:
    if not isinstance(value, list):
        fail(f"{context} must be an array")
    return cast(list[object], value)


def as_string(value: object, context: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a nonempty string")
    return value


def string_tuple(value: object, context: str) -> tuple[str, ...]:
    items = as_list(value, context)
    if not all(isinstance(item, str) and item for item in items):
        fail(f"{context} must contain only nonempty strings")
    return tuple(cast(list[str], items))


def closed_keys(value: dict[str, object], expected: set[str], context: str) -> None:
    if value.keys() != expected:
        fail(f"{context} keys are {sorted(value)}, expected {sorted(expected)}")


def enum_value(enum: type[EnumT], value: object, context: str) -> EnumT:
    text = as_string(value, context)
    try:
        return enum(text)
    except ValueError:
        fail(f"{context} has unknown value {text!r}")


def parse_relation(value: object, context: str) -> Relation:
    raw = as_object(value, context)
    closed_keys(raw, {"kind", "target"}, context)
    return Relation(
        enum_value(RelationKind, raw["kind"], f"{context}.kind"),
        as_string(raw["target"], f"{context}.target"),
    )


def parse_node(value: object, index: int) -> Node:
    context = f"nodes[{index}]"
    raw = as_object(value, context)
    closed_keys(
        raw,
        {
            "assurance",
            "href",
            "id",
            "kind",
            "origin",
            "prominence",
            "relations",
            "requires",
            "status",
            "summary",
            "title",
        },
        context,
    )
    if raw["status"] != "established":
        fail(f"{context}.status must be 'established' on a public graph")
    relations = tuple(
        parse_relation(item, f"{context}.relations[{relation_index}]")
        for relation_index, item in enumerate(
            as_list(raw["relations"], f"{context}.relations")
        )
    )
    assurance = enum_value(Assurance, raw["assurance"], f"{context}.assurance")
    if assurance not in {Assurance.FORMALIZED, Assurance.AUDITED}:
        fail(f"{context}.assurance must be 'formalized' or 'audited' publicly")
    return Node(
        as_string(raw["id"], f"{context}.id"),
        enum_value(NodeKind, raw["kind"], f"{context}.kind"),
        enum_value(Prominence, raw["prominence"], f"{context}.prominence"),
        enum_value(Origin, raw["origin"], f"{context}.origin"),
        assurance,
        as_string(raw["title"], f"{context}.title"),
        as_string(raw["summary"], f"{context}.summary"),
        as_string(raw["href"], f"{context}.href"),
        string_tuple(raw["requires"], f"{context}.requires"),
        relations,
    )


def parse_view(value: object, index: int) -> View:
    context = f"views[{index}]"
    raw = as_object(value, context)
    closed_keys(raw, {"id", "nodes", "summary", "title"}, context)
    return View(
        as_string(raw["id"], f"{context}.id"),
        as_string(raw["title"], f"{context}.title"),
        as_string(raw["summary"], f"{context}.summary"),
        string_tuple(raw["nodes"], f"{context}.nodes"),
    )


def parse_graph(path: Path) -> Graph:
    raw = as_object(json.loads(path.read_text()), str(path))
    closed_keys(raw, {"collection", "nodes", "version", "views"}, str(path))
    if raw["version"] != 1:
        fail(f"{path}: unsupported version")
    nodes = tuple(
        parse_node(value, index)
        for index, value in enumerate(as_list(raw["nodes"], "nodes"))
    )
    views = tuple(
        parse_view(value, index)
        for index, value in enumerate(as_list(raw["views"], "views"))
    )
    return Graph(as_string(raw["collection"], "collection"), nodes, views)


def publication_sources(manifest_path: Path) -> dict[str, Path]:
    raw = as_object(json.loads(manifest_path.read_text()), str(manifest_path))
    publications = as_list(raw.get("publications"), "publications")
    routes: dict[str, Path] = {}
    for index, value in enumerate(publications):
        entry = as_object(value, f"publications[{index}]")
        route_value = entry.get("route")
        if not isinstance(route_value, str):
            fail(f"publications[{index}].route must be a string")
        source = as_string(entry.get("source"), f"publications[{index}].source")
        routes[route_value] = manifest_path.parent / source
    return routes


def validate_href(node: Node, routes: dict[str, Path], collection: str) -> None:
    prefix = "/math/"
    if not node.href.startswith(prefix):
        fail(f"{node.id}: href must begin with {prefix}")
    path, separator, fragment = node.href.partition("#")
    route = path.removeprefix(prefix).rstrip("/")
    if route != collection and not route.startswith(f"{collection}/"):
        fail(f"{node.id}: href leaves collection {collection}")
    source = routes.get(route)
    if source is None:
        fail(f"{node.id}: href route {route!r} is unpublished")
    if separator and (not fragment or f'id="{fragment}"' not in source.read_text()):
        fail(f"{node.id}: missing fragment #{fragment} in {source.name}")


def validate_acyclic(nodes: dict[str, Node]) -> None:
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str) -> None:
        if node_id in visiting:
            fail(f"requires cycle reaches {node_id}")
        if node_id in visited:
            return
        visiting.add(node_id)
        for required in nodes[node_id].requires:
            visit(required)
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in nodes:
        visit(node_id)


def validate(graph: Graph, manifest_path: Path) -> dict[str, Node]:
    nodes = {node.id: node for node in graph.nodes}
    if len(nodes) != len(graph.nodes):
        fail("node identifiers must be unique")
    if any(not ID_PATTERN.fullmatch(node.id) for node in graph.nodes):
        fail("node identifiers must be semantic mm/ slugs")
    if len({view.id for view in graph.views}) != len(graph.views):
        fail("view identifiers must be unique")
    if any(not VIEW_PATTERN.fullmatch(view.id) for view in graph.views):
        fail("view identifiers must be semantic slugs")

    routes = publication_sources(manifest_path)
    if graph.collection not in routes:
        fail(f"collection route {graph.collection!r} is unpublished")
    for node in graph.nodes:
        validate_href(node, routes, graph.collection)
        targets = (*node.requires, *(relation.target for relation in node.relations))
        for target in targets:
            if target not in nodes:
                fail(f"{node.id}: unknown node target {target}")
    validate_acyclic(nodes)

    view_members = [node_id for view in graph.views for node_id in view.nodes]
    if len(view_members) != len(set(view_members)):
        fail("a node appears in more than one collection view")
    if set(view_members) != nodes.keys():
        fail("collection views must partition the public nodes")
    return nodes


def display(value: StrEnum) -> str:
    return value.value.replace("-", " ").title()


def kind_symbol(kind: NodeKind) -> str:
    match kind:
        case NodeKind.DEFINITION:
            return "≔"
        case NodeKind.CONSTRUCTION:
            return "⧉"
        case NodeKind.LEMMA:
            return "⊢"
        case NodeKind.REDUCTION:
            return "≤"
        case NodeKind.THEOREM:
            return "∎"
        case NodeKind.OBSTRUCTION:
            return "⊥"
        case NodeKind.WITNESS:
            return "∃"
        case _:
            assert_never(kind)


def render_toc(views: tuple[View, ...]) -> str:
    lines = [
        TOC_BEGIN,
        '        <li><a href="#modules">Modules</a>',
        "          <ol>",
    ]
    lines.extend(
        f'            <li><a href="#{view.id}">{html.escape(view.title)}</a></li>'
        for view in views
    )
    lines.extend(["          </ol>", "        </li>", TOC_END])
    return "\n".join(lines)


def relation_links(ids: tuple[str, ...], nodes: dict[str, Node]) -> str:
    return ", ".join(
        f'<a href="{html.escape(nodes[node_id].href, quote=True)}">'
        f"{html.escape(nodes[node_id].title)}</a>"
        for node_id in ids
    )


def render_node(
    node: Node, nodes: dict[str, Node], used_by: dict[str, tuple[str, ...]]
) -> str:
    lines = [
        '              <li class="module-node" '
        f'data-node-id="{html.escape(node.id, quote=True)}">',
        '                <p class="module-kind">',
        '                  <span class="module-kind-symbol" aria-hidden="true">'
        f"{html.escape(kind_symbol(node.kind))}</span>{display(node.kind)}",
        "                </p>",
        '                <p class="module-node-head">',
        f'                  <a href="{html.escape(node.href, quote=True)}">'
        f"<b>{html.escape(node.title)}</b></a>",
        "                </p>",
        f'                <p class="module-summary">{html.escape(node.summary)}</p>',
    ]
    relations: list[tuple[str, tuple[str, ...]]] = []
    if node.requires:
        relations.append(("Requires", node.requires))
    if used_by[node.id]:
        relations.append(("Used by", used_by[node.id]))
    relations.extend(
        (display(relation.kind), (relation.target,)) for relation in node.relations
    )
    if relations:
        lines.append('                <dl class="module-relations">')
        for label, targets in relations:
            lines.extend(
                [
                    "                  <div>",
                    f"                    <dt>{html.escape(label)}</dt>",
                    f"                    <dd>{relation_links(targets, nodes)}</dd>",
                    "                  </div>",
                ]
            )
        lines.append("                </dl>")
    lines.append("              </li>")
    return "\n".join(lines)


def render_graph(graph: Graph, nodes: dict[str, Node]) -> str:
    reverse: defaultdict[str, list[str]] = defaultdict(list)
    for node in graph.nodes:
        for required in node.requires:
            reverse[required].append(node.id)
    used_by = {node.id: tuple(reverse[node.id]) for node in graph.nodes}

    lines = [
        GRAPH_BEGIN,
        "        <section>",
        '          <h2 id="modules">Modules<a class="fragment-link" '
        'href="#modules" aria-label="Link to this section">#</a></h2>',
        "          <p>The constructions have two tasks. Source recognition encodes "
        "a halting computation as equality of words, then as a zero scalar "
        "coefficient. Target compression turns that test into mortality with fewer "
        "generators or coordinates. The arithmetic modules instead analyze "
        "particular families without settling their open table entries.</p>",
        "          <p>For the basic reduction, start with "
        '<a href="/math/matrix_mortality/m3_5/#four-tiles">the four word pairs</a> '
        'and their <a href="/math/matrix_mortality/m3_5/#five-matrices">five matrices</a>. '
        "Each card links to the relevant statement or construction, not necessarily "
        "the beginning of its article. Requires links give mathematical "
        "prerequisites, not a mandatory reading order.</p>",
        '          <dl class="module-legend">',
        "            <div><dt>Kind</dt><dd>What the box states: a definition, a "
        "construction, a lemma, a reduction (a correctness-preserving "
        "translation), a theorem (a principal conclusion), an obstruction (a "
        "proved limit), or a witness.</dd></div>",
        "            <div><dt>Edges</dt><dd>Requires and Used by are the proof "
        "dependencies; other named links, such as Instantiates and Strengthens, are "
        "cross-references, not dependencies.</dd></div>",
        "          </dl>",
        '          <div class="module-map">',
    ]
    for view in graph.views:
        lines.extend(
            [
                '            <section class="module-layer">',
                f'              <h3 id="{view.id}">{html.escape(view.title)}'
                f'<a class="fragment-link" href="#{view.id}" '
                'aria-label="Link to this section">#</a></h3>',
                f"              <p>{html.escape(view.summary)}</p>",
                '              <ol class="module-grid">',
            ]
        )
        lines.extend(
            render_node(nodes[node_id], nodes, used_by) for node_id in view.nodes
        )
        lines.extend(["              </ol>", "            </section>"])
    lines.extend(["          </div>", "        </section>", GRAPH_END])
    return "\n".join(lines)


def replace_region(source: str, begin: str, end: str, replacement: str) -> str:
    pattern = re.compile(f"{re.escape(begin)}.*?{re.escape(end)}", re.DOTALL)
    updated, count = pattern.subn(replacement, source)
    if count != 1:
        fail(f"expected exactly one {begin} region, found {count}")
    return updated


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--graph", type=Path, default=Path("matrix_mortality_modules.json")
    )
    parser.add_argument("--manifest", type=Path, default=Path("publications.json"))
    parser.add_argument("--landing", type=Path, default=Path("matrix_mortality.html"))
    args = parser.parse_args()

    try:
        graph = parse_graph(args.graph)
        nodes = validate(graph, args.manifest)
        source = args.landing.read_text()
        rendered = replace_region(source, TOC_BEGIN, TOC_END, render_toc(graph.views))
        rendered = replace_region(
            rendered, GRAPH_BEGIN, GRAPH_END, render_graph(graph, nodes)
        )
        if args.check:
            if rendered != source:
                fail(
                    f"{args.landing} does not match {args.graph}; "
                    f"run {Path(__file__).name}"
                )
        else:
            args.landing.write_text(rendered)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
