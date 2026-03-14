# License: Apache 2.0
# pylint: disable=R0912,R1702


# Standard Library Modules
import argparse
import json
from pathlib import Path
from typing import Any

# External Modules
try:
    import matplotlib.pyplot as plt
    import networkx as nx
    from matplotlib.patches import Patch

    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

try:
    from pyvis.network import Network

    PYVIS_AVAILABLE = True
except ImportError:
    PYVIS_AVAILABLE = False


def truncate_label(label: str, max_length: int) -> str:
    """Truncate label for display while preserving readability."""
    if len(label) <= max_length:
        return label

    # Try to break at word boundaries
    words = label.split()
    if len(words) > 1 and len(words[0]) < max_length - 3:
        result = words[0]
        for word in words[1:]:
            if len(result) + len(word) + 4 < max_length:  # +4 for " " and "..."
                result += " " + word
            else:
                return result + "..."
        return result

    # Simple truncation
    return label[: max_length - 3] + "..."


def create_interactive_cdg_visualization(cdg: dict[str, dict[str, Any]], output_path: str = "cdg_visualization.html") -> None:
    """Create an interactive HTML visualization showing hierarchical dependency structure."""
    if not PYVIS_AVAILABLE:
        raise ImportError("pyvis not available")

    # Create network with hierarchical layout
    net = Network(height="900px", width="100%", bgcolor="#fafafa", font_color="black", directed=True, layout=True)

    # Node colors and styles
    colors = {
        "concept": "#3498db",  # Blue for concepts
        "formal_correspondent": "#27ae60",  # Green for DSL elements (leaf nodes)
        "dependency": "#e74c3c",  # Red for unresolved dependencies
    }

    added_nodes = set()
    edge_count = 0

    # Track concept groups for clustering/grouped dragging
    concept_groups: dict[str, int] = {}
    group_id = 0

    # First pass: collect all unique formal correspondents and their parent concepts
    all_correspondents: dict[str, list[str]] = {}  # correspondent -> list of parent concepts
    for concept_name, concept_data in cdg.items():
        formal_correspondents = concept_data.get("formal_correspondents", [])
        for correspondent in formal_correspondents:
            if correspondent not in all_correspondents:
                all_correspondents[correspondent] = []
            all_correspondents[correspondent].append(concept_name)

    def add_concept_tree(
        concept_name: str,
        concept_data: dict[str, Any],
        level: int = 0,
        concept_positions: dict | None = None,
        dsl_positions: dict | None = None,
        middle_y: float = 0,
        parent_group: int | None = None,
    ) -> int:
        """Recursively add concept and its dependencies/correspondents as a tree with group clustering."""
        nonlocal edge_count, group_id

        if concept_name in added_nodes:
            return concept_groups.get(concept_name, parent_group or 0)

        # Assign group ID for this concept family
        current_group = parent_group if parent_group is not None else group_id
        if parent_group is None:
            group_id += 1

        concept_groups[concept_name] = current_group

        # Add the main concept node
        formal_correspondents = concept_data.get("formal_correspondents", [])
        concept_dependencies = concept_data.get("concept_dependencies", [])
        analysis = concept_data.get("analysis", "No analysis available")
        status = concept_data.get("status", "unknown")

        tooltip = (
            f"<b>CONCEPT: {concept_name}</b><br>"
            f"<b>Status:</b> {status}<br>"
            f"<b>Dependencies:</b> {len(concept_dependencies)}<br>"
            f"<b>DSL Elements:</b> {len(formal_correspondents)}<br><br>"
            f"<b>Analysis:</b><br>{analysis[:200]}{'...' if len(analysis) > 200 else ''}<br><br>"
            f"<i>💡 Drag this concept freely to move it with its connected DSL elements!</i>"
        )

        # Get initial position for this concept
        node_params = {
            "label": truncate_label(concept_name, 60),
            "color": {
                "background": "rgba(52, 152, 219, 0.3)",  # Light blue with high transparency
                "border": colors["concept"],
                "highlight": {"background": "rgba(52, 152, 219, 0.5)", "border": colors["concept"]},
            },
            "size": 150,  # Much larger size for concepts
            "title": tooltip,
            "font": {
                "size": 22,
                "color": "black",
                "bold": True,
                "strokeWidth": 2,
                "strokeColor": "white",
            },  # Black text with white outline for visibility
            "borderWidth": 4,
            "shape": "box",  # Square shape for concepts
            "physics": False,  # Allow manual positioning
        }

        # Add initial position if available
        if concept_positions and concept_name in concept_positions:
            node_params["x"] = concept_positions[concept_name]["x"]
            node_params["y"] = concept_positions[concept_name]["y"]

        net.add_node(concept_name, **node_params)
        added_nodes.add(concept_name)

        # Add formal correspondents as shared leaf nodes (green) positioned below concepts
        for i, correspondent in enumerate(formal_correspondents):
            correspondent_id = f"dsl_{correspondent}"
            if correspondent_id not in added_nodes:
                # Get all parent concepts for this correspondent
                parent_concepts = all_correspondents.get(correspondent, [concept_name])
                sharing_info = f"<br><b>Shared by:</b> {', '.join(parent_concepts)}" if len(parent_concepts) > 1 else ""

                # Calculate position below the parent concept
                dsl_params = {
                    "label": truncate_label(correspondent, 35),
                    "color": {
                        "background": "rgba(39, 174, 96, 0.3)",  # Light green with high transparency
                        "border": colors["formal_correspondent"],
                        "highlight": {"background": "rgba(39, 174, 96, 0.5)", "border": colors["formal_correspondent"]},
                    },
                    "size": 50,  # Slightly larger size for better text visibility
                    "title": (
                        f"<b>DSL ELEMENT</b><br>{correspondent}{sharing_info}<br><br>"
                        f"<i>{'Shared across multiple concepts' if len(parent_concepts) > 1 else 'DSL Implementation'}</i>"
                    ),
                    "font": {
                        "size": 14,
                        "color": "black",
                        "bold": True,
                        "strokeWidth": 1,
                        "strokeColor": "white",
                    },  # Black text with white outline for visibility
                    "shape": "ellipse",  # Keep ellipse for better text display
                    "borderWidth": 3,
                }

                # Position DSL element in the middle layer
                if concept_positions and concept_name in concept_positions and dsl_positions is not None:
                    parent_x = concept_positions[concept_name]["x"]

                    # Position DSL elements in the middle layer, spread horizontally
                    dsl_x = parent_x + (i - len(formal_correspondents) / 2) * 80  # Wider horizontal spread
                    dsl_y = middle_y  # Middle layer position

                    # Avoid overlaps with existing DSL elements
                    overlap_found = True
                    offset = 0
                    while overlap_found:
                        overlap_found = False
                        for existing_pos in dsl_positions.values():
                            if abs(existing_pos["x"] - dsl_x) < 100 and abs(existing_pos["y"] - dsl_y) < 60:
                                offset += 60
                                dsl_x = parent_x + (i - len(formal_correspondents) / 2) * 120 + offset
                                overlap_found = True
                                break

                    dsl_params["x"] = dsl_x
                    dsl_params["y"] = dsl_y

                    # Track this position to avoid overlaps
                    dsl_positions[correspondent_id] = {"x": dsl_x, "y": dsl_y}

                net.add_node(correspondent_id, **dsl_params)
                added_nodes.add(correspondent_id)

            # Connect concept to its DSL elements with hierarchical binding
            net.add_edge(
                concept_name,
                correspondent_id,
                arrows="to",
                color="#27ae60",
                width=2,
                length=150,  # Hierarchical edge length
                spring={"length": 150, "constant": 0.3},  # Spring for grouped movement
            )
            edge_count += 1

        # Add concept dependencies recursively with grouping
        for dep_name in concept_dependencies:
            if dep_name in cdg:
                # Recursively add the dependency concept with the same group
                dep_data = cdg[dep_name]
                add_concept_tree(dep_name, dep_data, level + 1, concept_positions, dsl_positions, middle_y, current_group)

                # Connect this concept to its dependency
                net.add_edge(
                    concept_name,
                    dep_name,
                    arrows="to",
                    color="#3498db",
                    width=3,
                    length=200,  # Longer edge for concept dependencies
                    spring={"length": 200, "constant": 0.1},  # Weaker spring for concept connections
                )
                edge_count += 1
            else:
                # Add unresolved dependency as a red node in the same group
                dep_id = f"unresolved_{dep_name}"
                if dep_id not in added_nodes:
                    net.add_node(
                        dep_id,
                        label=truncate_label(dep_name, 30),
                        color={
                            "background": "rgba(231, 76, 60, 0.3)",  # Light red with high transparency
                            "border": colors["dependency"],
                            "highlight": {"background": "rgba(231, 76, 60, 0.5)", "border": colors["dependency"]},
                        },
                        size=40,  # Slightly larger for consistency
                        title=f"<b>UNRESOLVED DEPENDENCY</b><br>{dep_name}<br><br><i>Missing dependency</i>",
                        font={"size": 12, "color": "black", "bold": True, "strokeWidth": 1, "strokeColor": "white"},
                        shape="triangle",  # Triangle shape for unresolved dependencies
                        borderWidth=3,
                        # Remove physics=False to allow binding to parent concepts
                    )
                    added_nodes.add(dep_id)

                net.add_edge(
                    concept_name,
                    dep_id,
                    arrows="to",
                    color="#e74c3c",
                    width=2,
                    length=150,  # Hierarchical edge length
                    spring={"length": 150, "constant": 0.25},  # Spring for grouped movement
                )
                edge_count += 1

        return current_group

    # Build the complete dependency trees for all concepts with manual sandwich positioning
    print("Building sandwich layout: concepts-DSL-concepts...")

    # Calculate positions for sandwich layout (2 rows of concepts with DSL elements in between)
    concept_list = list(cdg.keys())
    concept_count = len(concept_list)

    # Split concepts into two rows
    concepts_per_row = max(1, concept_count // 2 + concept_count % 2)  # Round up for first row
    top_concepts = concept_list[:concepts_per_row]
    bottom_concepts = concept_list[concepts_per_row:]

    # Layout settings
    concept_spacing = 400  # MASSIVE horizontal spacing between concepts to guarantee no overlap
    top_y = -400  # Top row position (massively far apart)
    middle_y = 0  # DSL elements position (middle)
    bottom_y = 400  # Bottom row position (massively far apart)

    concept_positions: dict[str, dict[str, float]] = {}

    # Position top row of concepts
    if top_concepts:
        start_x_top = -(len(top_concepts) - 1) * concept_spacing / 2
        for i, concept_name in enumerate(top_concepts):
            x_pos = start_x_top + i * concept_spacing
            concept_positions[concept_name] = {"x": x_pos, "y": top_y}

    # Position bottom row of concepts
    if bottom_concepts:
        start_x_bottom = -(len(bottom_concepts) - 1) * concept_spacing / 2
        for i, concept_name in enumerate(bottom_concepts):
            x_pos = start_x_bottom + i * concept_spacing
            concept_positions[concept_name] = {"x": x_pos, "y": bottom_y}

    # Track DSL element positions in the middle layer
    dsl_positions: dict[str, dict[str, float]] = {}

    for concept_name, concept_data in cdg.items():
        add_concept_tree(concept_name, concept_data, 0, concept_positions, dsl_positions, middle_y)

    # Configure physics for free dragging with organized initial layout
    net.set_options(
        """
    var options = {
      "physics": {
        "enabled": true,
        "stabilization": {
          "enabled": true,
          "iterations": 50,
          "updateInterval": 25,
          "onlyDynamicEdges": false,
          "fit": true
        },
        "forceAtlas2Based": {
          "gravitationalConstant": -20,
          "centralGravity": 0.01,
          "springConstant": 0.08,
          "springLength": 100,
          "damping": 0.4,
          "avoidOverlap": 0.5
        },
        "solver": "forceAtlas2Based"
      },
      "layout": {
        "improvedLayout": true,
        "hierarchical": {
          "enabled": false
        }
      },
      "interaction": {
        "dragNodes": true,
        "dragView": true,
        "zoomView": true,
        "hover": true,
        "selectConnectedEdges": true,
        "tooltipDelay": 100,
        "multiselect": true,
        "keyboard": {
          "enabled": true,
          "speed": {
            "x": 10,
            "y": 10,
            "zoom": 0.02
          }
        }
      },
      "manipulation": {
        "enabled": false
      },
      "edges": {
        "smooth": {
          "type": "dynamic",
          "forceDirection": "none",
          "roundness": 0.1
        },
        "physics": true,
        "selectionWidth": 3
      },
      "nodes": {
        "physics": true
      },
      "groups": {
        "useDefaultGroups": true
      }
    }
    """
    )

    # Create title with better information
    total_concepts = len(cdg)
    total_formal_elements = sum(len(data.get("formal_correspondents", [])) for data in cdg.values())
    total_dependencies = sum(len(data.get("concept_dependencies", [])) for data in cdg.values())

    title = (
        "<h2>Interactive Concept Dependency Hierarchy</h2>"
        f"<p><strong>Concepts:</strong> {total_concepts} | "
        f"<strong>DSL Elements:</strong> {total_formal_elements} | "
        f"<strong>Dependencies:</strong> {total_dependencies} | "
        f"<strong>Connections:</strong> {edge_count}</p>"
        "<p>"
        f'<span style="color: {colors["concept"]}; font-weight: bold;">● Concepts (Blue)</span> | '
        f'<span style="color: {colors["formal_correspondent"]}; font-weight: bold;">● DSL Elements (Green)</span> | '
        f'<span style="color: {colors["dependency"]}; font-weight: bold;">● Unresolved (Red)</span>'
        "</p>"
        "<p><strong>📋 Layout:</strong> Sandwich design - blue concepts (top row), green DSL elements (middle), blue concepts (bottom row)</p>"
        "<p><strong>🎯 Interactive Features:</strong></p>"
        "<ul>"
        "<li><strong>Drag Concepts:</strong> Drag blue concept boxes to move them with their connected DSL elements</li>"
        "<li><strong>Multi-select:</strong> Hold Ctrl/Cmd and click to select multiple nodes</li>"
        "<li><strong>Zoom & Pan:</strong> Scroll to zoom, drag background to pan</li>"
        "<li><strong>Hover:</strong> Hover over nodes for detailed information</li>"
        "</ul>"
        "<p><em>Sandwich layout with generous spacing and freely draggable concept boxes! DSL elements positioned between concept rows.</em></p>"
    )

    # Save and open the visualization
    net.save_graph(output_path)

    # Add custom title to the HTML file
    with open(output_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Insert title after body tag
    content = content.replace("<body>", f"<body>{title}")

    with open(output_path, "w", encoding="utf-8") as f:
        f.write(content)

    print(f"✅ Interactive CDG visualization saved to {output_path}")
    print(f"📊 Summary: {total_concepts} concepts, {total_formal_elements} DSL elements, {edge_count} connections")
    print("🎯 Features: Sandwich layout with wide spacing and freely draggable concept groups")

    print(f"💡 Open {output_path} in your browser to drag concepts and explore dependencies interactively!")


def create_static_cdg_visualization(cdg: dict[str, dict[str, Any]], output_path: str = "cdg_visualization.png") -> None:
    """Create a clear static visualization showing hierarchical dependency structure."""
    if not MATPLOTLIB_AVAILABLE:
        raise ImportError("matplotlib/networkx not available")

    # Create directed graph
    G = nx.DiGraph()

    # Define colors for different node types (lighter, more visible colors)
    colors = {
        "concept": "#2E86AB",  # Dark blue for concepts
        "formal_correspondent": "#A23B72",  # Magenta for DSL elements
        "dependency": "#F18F01",  # Orange for unresolved dependencies
    }

    # Collect all nodes and their metadata
    node_metadata = {}

    # First pass: collect all unique concepts and DSL elements
    unique_concepts = set()
    unique_dsl_elements = set()
    unresolved_deps = set()

    for concept_name, concept_data in cdg.items():
        unique_concepts.add(concept_name)

        formal_correspondents = concept_data.get("formal_correspondents", [])
        for fc in formal_correspondents:
            unique_dsl_elements.add(fc)

        concept_dependencies = concept_data.get("concept_dependencies", [])
        for dep in concept_dependencies:
            if dep not in cdg:
                unresolved_deps.add(dep)

    # Add nodes to graph with much larger sizes for readability
    for concept in unique_concepts:
        G.add_node(concept, node_type="concept")
        node_metadata[concept] = {"type": "concept", "color": colors["concept"], "size": 8000, "shape": "s"}

    for dsl_elem in unique_dsl_elements:
        node_id = f"dsl_{dsl_elem}"
        G.add_node(node_id, node_type="dsl")
        node_metadata[node_id] = {"type": "dsl", "color": colors["formal_correspondent"], "size": 5000, "shape": "o"}

    for unres_dep in unresolved_deps:
        node_id = f"unres_{unres_dep}"
        G.add_node(node_id, node_type="unresolved")
        node_metadata[node_id] = {"type": "unresolved", "color": colors["dependency"], "size": 4000, "shape": "^"}

    # Add edges
    for concept_name, concept_data in cdg.items():
        # Connect to DSL elements
        formal_correspondents = concept_data.get("formal_correspondents", [])
        for fc in formal_correspondents:
            dsl_node = f"dsl_{fc}"
            if dsl_node in G:
                G.add_edge(concept_name, dsl_node)

        # Connect to dependencies
        concept_dependencies = concept_data.get("concept_dependencies", [])
        for dep in concept_dependencies:
            if dep in cdg:
                G.add_edge(concept_name, dep)
            else:
                unres_node = f"unres_{dep}"
                if unres_node in G:
                    G.add_edge(concept_name, unres_node)

    # Calculate optimal figure size based on number of nodes (much larger for readability)
    num_nodes = len(G.nodes())
    base_size = max(36, min(72, num_nodes * 1.8))  # Much larger base size for big nodes
    plt.figure(figsize=(base_size, base_size * 0.8), facecolor="white")

    # Create better layout
    try:
        # Try hierarchical layout first
        levels = {}
        for node in nx.topological_sort(G):
            predecessors = list(G.predecessors(node))
            if not predecessors:
                levels[node] = 0
            else:
                levels[node] = max(levels[pred] for pred in predecessors) + 1

        # Group nodes by level and spread them out
        level_nodes: dict[int, list[str]] = {}
        for node, level in levels.items():
            if level not in level_nodes:
                level_nodes[level] = []
            level_nodes[level].append(node)

        pos = {}
        level_separation = 8.0  # Much more separation between levels
        node_separation = 6.0  # Much more separation between nodes

        for level, nodes in level_nodes.items():
            num_nodes_in_level = len(nodes)
            total_width = (num_nodes_in_level - 1) * node_separation
            start_x = -total_width / 2

            for i, node in enumerate(nodes):
                x = start_x + i * node_separation
                y = -level * level_separation
                pos[node] = (x, y)

    except nx.NetworkXError:
        # Fallback to spring layout with better parameters for larger nodes
        pos = nx.spring_layout(G, k=8.0, iterations=300, seed=42)

    # Separate nodes by type for different drawing
    concept_nodes = [n for n in G.nodes() if node_metadata[n]["type"] == "concept"]
    dsl_nodes = [n for n in G.nodes() if node_metadata[n]["type"] == "dsl"]
    unres_nodes = [n for n in G.nodes() if node_metadata[n]["type"] == "unresolved"]

    # Draw edges first (so they appear behind nodes)
    edge_colors = []
    edge_widths = []
    for edge in G.edges():
        _, target = edge
        if node_metadata[target]["type"] == "dsl":
            edge_colors.append("#A23B72")  # Magenta for DSL connections
            edge_widths.append(5)
        elif node_metadata[target]["type"] == "concept":
            edge_colors.append("#2E86AB")  # Blue for concept dependencies
            edge_widths.append(4)
        else:
            edge_colors.append("#F18F01")  # Orange for unresolved
            edge_widths.append(4)

    nx.draw_networkx_edges(G, pos, edge_color=edge_colors, width=edge_widths, arrows=True, arrowsize=60, arrowstyle="->", alpha=0.7)

    # Draw nodes by type with high visibility and much larger sizes
    if concept_nodes:
        nx.draw_networkx_nodes(
            G, pos, nodelist=concept_nodes, node_color=colors["concept"], node_size=8000, node_shape="s", alpha=0.9, edgecolors="black", linewidths=6
        )

    if dsl_nodes:
        nx.draw_networkx_nodes(
            G,
            pos,
            nodelist=dsl_nodes,
            node_color=colors["formal_correspondent"],
            node_size=5000,
            node_shape="o",
            alpha=0.9,
            edgecolors="black",
            linewidths=3,
        )

    if unres_nodes:
        nx.draw_networkx_nodes(
            G, pos, nodelist=unres_nodes, node_color=colors["dependency"], node_size=4000, node_shape="^", alpha=0.9, edgecolors="black", linewidths=5
        )

    # Create clear labels with longer text for larger nodes
    labels = {}
    for node in G.nodes():
        if node_metadata[node]["type"] == "concept":
            labels[node] = truncate_label(node, 20)  # Longer labels for concepts
        elif node_metadata[node]["type"] == "dsl":
            # Remove "dsl_" prefix for display
            clean_name = node[4:] if node.startswith("dsl_") else node
            labels[node] = truncate_label(clean_name, 15)  # Longer labels for DSL
        else:
            # Remove "unres_" prefix for display
            clean_name = node[6:] if node.startswith("unres_") else node
            labels[node] = truncate_label(clean_name, 15)  # Longer labels

    # Draw labels with much better visibility and larger fonts
    nx.draw_networkx_labels(
        G,
        pos,
        labels,
        font_size=24,  # Much larger font
        font_weight="bold",
        font_color="white",
        bbox={"boxstyle": "round,pad=0.3", "facecolor": "black", "alpha": 0.8, "edgecolor": "white", "linewidth": 1},
    )

    # Create a comprehensive legend
    legend_elements = [
        Patch(facecolor=colors["concept"], edgecolor="black", linewidth=2, label=f"Concepts ({len(concept_nodes)})"),
        Patch(facecolor=colors["formal_correspondent"], edgecolor="black", linewidth=2, label=f"DSL Elements ({len(dsl_nodes)})"),
        Patch(facecolor=colors["dependency"], edgecolor="black", linewidth=2, label=f"Unresolved Dependencies ({len(unres_nodes)})"),
    ]

    plt.legend(handles=legend_elements, loc="upper left", bbox_to_anchor=(1.02, 1), fontsize=20, frameon=True, fancybox=True, shadow=True)

    # Better title and formatting with larger font
    plt.title("Concept Dependency Graph\nConcepts (squares) → DSL Elements (circles) & Dependencies", fontsize=32, fontweight="bold", pad=40)

    plt.axis("off")
    plt.tight_layout()

    # Save with high quality and no plt.show() to avoid interference
    plt.savefig(output_path, dpi=300, bbox_inches="tight", facecolor="white", edgecolor="none", format="png")
    plt.close()  # Close the figure to free memory

    print(f"✅ Static CDG visualization saved to {output_path}")
    print(f"📊 Summary: {len(concept_nodes)} concepts, {len(dsl_nodes)} DSL elements, {len(unres_nodes)} unresolved deps")
    print(f"🎨 High-resolution PNG with EXTRA LARGE nodes and readable text - node sizes: concepts={8000}, DSL={5000}, deps={4000}")
    print("📖 Font size: 24pt with high-contrast labels for maximum readability")


def create_text_cdg_summary(cdg: dict[str, dict[str, Any]], output_file: str | None = None) -> None:
    """Create a detailed text-based summary of the CDG hierarchy."""
    # Build the summary content
    lines = []
    lines.append("\n" + "=" * 80)
    lines.append("CONCEPT DEPENDENCY GRAPH HIERARCHY")
    lines.append("=" * 80)

    total_concepts = len(cdg)
    total_formal_elements = sum(len(data.get("formal_correspondents", [])) for data in cdg.values())
    total_dependencies = sum(len(data.get("concept_dependencies", [])) for data in cdg.values())

    lines.append(f"Total Concepts: {total_concepts}")
    lines.append(f"Total DSL Elements: {total_formal_elements}")
    lines.append(f"Total Dependencies: {total_dependencies}")
    lines.append("")

    # Show each concept and its structure
    for concept_name, concept_data in cdg.items():
        status = concept_data.get("status", "unknown")
        formal_correspondents = concept_data.get("formal_correspondents", [])
        concept_dependencies = concept_data.get("concept_dependencies", [])

        lines.append(f"📦 {concept_name[:60]}... [{status}]")

        if formal_correspondents:
            lines.append("   ├─ DSL Elements:")
            for fc in formal_correspondents:
                lines.append(f"   │  └─ 🟢 {fc[:50]}...")

        if concept_dependencies:
            lines.append("   ├─ Dependencies:")
            for dep in concept_dependencies:
                if dep in cdg:
                    lines.append(f"   │  └─ 🔗 {dep[:50]}... (in CDG)")
                else:
                    lines.append(f"   │  └─ 🔴 {dep[:50]}... (unresolved)")

        if not formal_correspondents and not concept_dependencies:
            lines.append("   └─ (no dependencies or DSL elements)")

        lines.append("")

    lines.append("=" * 80)
    lines.append("Legend: 🟢 = DSL Element (leaf), 🔗 = Concept Dependency, 🔴 = Unresolved Dependency")

    # Print to console
    summary_text = "\n".join(lines)
    print(summary_text)

    # Write to file if specified
    if output_file:
        try:
            with open(output_file, "w", encoding="utf-8") as f:
                f.write(summary_text)
            print(f"\n✅ Text summary saved to {output_file}")
        except Exception as e:
            print(f"\n⚠️ Failed to write summary to {output_file}: {e}")


def visualize_cdg(cdg: dict[str, dict[str, Any]], output_dir: str = ".", filename: str = "cdg_visualization") -> None:
    """
    Create hierarchical visualizations of the Concept Dependency Graph (CDG).

    Shows concepts as parents to their formal_correspondents (DSL elements) and concept_dependencies.
    Builds a proper hierarchy where formal_correspondents are leaf nodes and dependencies recurse.
    """
    if not cdg:
        print("No concepts to visualize - CDG is empty")
        return

    # Create output paths with custom filename
    html_output = Path(output_dir) / f"{filename}.html"
    png_output = Path(output_dir) / f"{filename}.png"

    try:
        # Try to create interactive visualization with pyvis
        create_interactive_cdg_visualization(cdg, str(html_output))
    except ImportError:
        print("⚠️  pyvis not available, skipping interactive visualization...")

    try:
        # Try to create static visualization with networkx + matplotlib
        create_static_cdg_visualization(cdg, str(png_output))
    except ImportError:
        print("⚠️  networkx/matplotlib not available, skipping static visualization...")

    # Always create text summary (both console and file)
    text_output = Path(output_dir) / f"{filename}_summary.txt"
    create_text_cdg_summary(cdg, str(text_output))


def main() -> None:
    """Main function to visualize a Concept Dependency Graph from a JSON file."""
    parser = argparse.ArgumentParser(
        description="Visualize a Concept Dependency Graph (CDG) from a JSON file",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--input_file",
        type=str,
        default="UniGeo/outputs/cdg_UniGeo_qwen3.json",
        help="Path to the CDG JSON file to visualize",
    )
    parser.add_argument(
        "--output_path",
        type=str,
        default="./cdg",
        help="Directory path where visualization files will be saved (default: ./cdg)",
    )
    parser.add_argument(
        "--filename",
        type=str,
        default="cdg_visualization",
        help="Base filename for output files (extensions .html/.png will be added automatically) (default: cdg_visualization)",
    )
    args = parser.parse_args()

    # Load the CDG from JSON file
    try:
        with open(args.input_file, "r", encoding="utf-8") as f:
            cdg = json.load(f)
    except FileNotFoundError:
        print(f"Error: File '{args.input_file}' not found.")
        return
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.input_file}': {e}")
        return
    except Exception as e:
        print(f"Error loading '{args.input_file}': {e}")
        return

    # Validate CDG structure
    if not isinstance(cdg, dict):
        print("Error: CDG must be a dictionary")
        return

    if not cdg:
        print("Warning: CDG is empty")
        return

    print(f"Loading CDG from {args.input_file}...")
    print(f"Found {len(cdg)} concepts in the CDG")

    # Create output directory if it doesn't exist
    output_path = Path(args.output_path)
    output_path.mkdir(parents=True, exist_ok=True)

    # Create visualization
    visualize_cdg(cdg, args.output_path, args.filename)


if __name__ == "__main__":
    main()
