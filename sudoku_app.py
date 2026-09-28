import json
import time
import streamlit as st
from utils import *
from logic_ import *
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails)

st.title('Sudoku Solver')

with open('puzzles.json') as f:
    pool = json.load(f)

n = pool['n']
box_h = pool['box_h']
box_w = pool['box_w']

# --- 1. Puzzle selection & visual board display ---

st.subheader("Sudoku Puzzle Selection and Visual Board Display")

puzzle_index = st.selectbox(
    "Select a puzzle",
    range(len(pool["puzzles"])),
    format_func=lambda i: f"Puzzle {i + 1}")

puzzle = pool["puzzles"][puzzle_index]

givens = {tuple(int(x) for x in key.split("_")): value
    for key, value in puzzle["givens"].items()}

board = "<table style='border-collapse: collapse;'>"

for r in range(1, n + 1):
    board += "<tr>"
    for c in range(1, n + 1):
        if (r, c) in givens:
            value = f"<b>{givens[(r, c)]}</b>"
        else:
            value = ""

        top = 3 if r in [1, 4, 7] else 1
        left = 3 if c in [1, 4, 7] else 1
        bottom = 3 if r in [3, 6, 9] else 1
        right = 3 if c in [3, 6, 9] else 1

        board += f"<td style='width:50px; height:50px; text-align:center; border-top:{top}px solid black; border-left:{left}px solid black; border-bottom:{bottom}px solid black; border-right:{right}px solid black;'>{value}</td>"

    board += "</tr>"

board += "</table>"

st.markdown(board, unsafe_allow_html=True)

# --- 2. Full-grid auto-solver, with algorithm selection ---

st.subheader("Full-Grid Auto-Solver")

algorithm = st.radio(
    "Choose an algorithm:",
    ["Forward Chaining", "Backward Chaining"])

if st.button("Solve Full Grid"):

    start = time.time()

    if algorithm == "Forward Chaining":
        solution = solve_full_grid_fc(
            n, pool["box_h"], pool["box_w"], givens)
    else:
        solution = solve_full_grid_bc(
            n, pool["box_h"], pool["box_w"], givens)

    end = time.time()
    st.write(f"Solve time: {end - start:.4f} seconds")

    st.subheader("Solved Board")

    board = "<table style='border-collapse: collapse;'>"

    for r in range(1, n + 1):
        board += "<tr>"

        for c in range(1, n + 1):
            value = solution.get((r, c), "")
            if (r, c) in givens:
                value = f"<b>{value}</b>"

            top = 3 if r in [1, 4, 7] else 1
            left = 3 if c in [1, 4, 7] else 1
            bottom = 3 if r in [3, 6, 9] else 1
            right = 3 if c in [3, 6, 9] else 1

            board += f"<td style='width:50px; height:50px; text-align:center; border-top:{top}px solid black; border-left:{left}px solid black; border-bottom:{bottom}px solid black; border-right:{right}px solid black;'>{value}</td>"

        board += "</tr>"

    board += "</table>"

    st.markdown(board, unsafe_allow_html=True)

# --- 3. Targeted cell entailment query ---

st.subheader("Targeted Cell Entailment Query")

r = st.number_input("Row", min_value=1, max_value=n, value=1)
c = st.number_input("Column", min_value=1, max_value=n, value=1)
v = st.number_input("Value", min_value=1, max_value=n, value=1)

if st.button("Check Entailment"):
    kb = build_definite_kb(
        n,
        pool["box_h"],
        pool["box_w"],
        givens)

    query = atom("Is", r, c, v)
    result = pl_bc_entails(kb, query)
    st.write("Entailed:", result)

# --- 4. Reasoning trace ("tutor mode") ---

st.subheader("Reasoning Trace (Tutor Mode)")

def explain_query(r, c, v, givens, box_h, box_w):
    # If the cell is already given
    if (r, c) in givens:
        if givens[(r, c)] == v:
            return []
        return [f"Cell ({r}, {c}) is already given as {givens[(r, c)]}."]

    steps = []

    # Check row and column
    for (row, col), value in givens.items():
        if row == r and value == v:
            steps.append(f"Row {r} already contains {v} at cell ({row}, {col}).")
        if col == c and value == v:
            steps.append(f"Column {c} already contains {v} at cell ({row}, {col}).")

    start_r = ((r - 1) // box_h) * box_h + 1
    start_c = ((c - 1) // box_w) * box_w + 1

    for (row, col), value in givens.items():
        if (start_r <= row < start_r + box_h
            and start_c <= col < start_c + box_w
            and value == v):
            steps.append(
                f"The same {box_h}×{box_w} box already contains {v} "
                f"at cell ({row}, {col}).")

    return steps

tutor_r = st.number_input(
    "Row", 1, n, 1, key="tutor_row")
tutor_c = st.number_input(
    "Column", 1, n, 1, key="tutor_column")
tutor_v = st.number_input(
    "Value", 1, n, 1, key="tutor_value")

if st.button("Show Reasoning", key="tutor_button"):
    r = int(tutor_r)
    c = int(tutor_c)
    v = int(tutor_v)

    st.markdown("**🎯 Goal**")
    st.write(f"Determine whether **Row {r}, Column {c} can contain {v}**.")

    steps = explain_query(r, c, v, givens, box_h, box_w)

    if (r, c) in givens and v == givens[(r, c)]:
        st.success(
            f"Cell ({r}, {c}) is an initial given with value **{v}**.")
    elif steps:
        st.error(
            f"Value {v} cannot be placed at Row {r}, Column {c}.")
        st.markdown("**Why?**")
        for i, step in enumerate(steps, 1):
            with st.expander(f"Step {i} — Eliminate {v}", expanded=True):
                st.write(step)
    else:
        st.info(
            f"No direct row, column, or box conflict eliminates {v}.")

    possible = []
    eliminated = []

    for candidate in range(1, n + 1):
        if (r, c) in givens:
            can_use = candidate == givens[(r, c)]
        else:
            can_use = not explain_query(
                r, c, candidate, givens, box_h, box_w)
        if can_use:
            possible.append(candidate)
        else:
            eliminated.append(candidate)

    st.markdown("**Candidate Analysis**")

    cols = st.columns(n)
    for i, candidate in enumerate(range(1, n + 1)):
        symbol = "🟢" if candidate in possible else "❌"
        with cols[i]:
            st.markdown(
                f"<div style='text-align:center;'>"
                f"{symbol}<br><b>{candidate}</b>"
                f"</div>",
                unsafe_allow_html=True)

    st.markdown("**Final Deduction**")

    if (r, c) in givens:
        st.success(
            f"Cell ({r}, {c}) is fixed as **{givens[(r, c)]}**.")
    elif len(possible) == 1:
        st.success(
            f"Only **{possible[0]}** remains, so "
            f"**Row {r}, Column {c} = {possible[0]}**.")
    elif possible:
        st.info(
            f"Remaining candidates: "
            f"**{', '.join(map(str, possible))}**.")
    else:
        st.warning("No candidates remain. This indicates a contradiction.")