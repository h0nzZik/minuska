# Minuska Developer Guide

## Introduction

Welcome to the Minuska Developer Guide! This document is intended for developers who wish to contribute to or modify Minuska. It provides an overview of the architecture, development setup, and code structure to help you get started.

## Architecture Overview

Minuska is a formally verified semantics framework built on top of the Coq proof assistant. Its architecture consists of the following key components:

- **Coq Core**: The heart of Minuska, where the formally verified components live.
- **OCaml Integration**: Manually written OCaml components, alongside the Coq-extracted OCaml code, forms the runtime and tooling for Minuska.
- **Nix Build System**: Nix is used to manage dependencies and ensure reproducibility across different environments. It orchestrates the build process for both Coq and OCaml components.

The interaction between Coq and OCaml is a critical part of the architecture. For example, files like `Dsm.ml` and `Dsm.mli` are generated from Coq definitions (see [flake.nix](../flake.nix)) and integrated into the OCaml build process.

## Development Setup

The development environment setup depends on the component you want to work on:

- **Coq Development**:
  - Use the `coq-minuska` development shell:
    ```sh
    nix develop '.#coq-minuska'
    ```
  - This provides the required Coq version, libraries, and tools like `coqide` and `coq-lsp`.

- **OCaml Development**:
  - Use the `minuska` development shell:
    ```sh
    nix develop '.#minuska'
    ```
  - This includes the OCaml compiler, libraries, and tools like `dune`. Crucially, `Dsm.ml` and `Dsm.mli` (needed to build the OCaml component) are generated from the Coq sources.

- **Benchmarks**:
  - Use the `bench-standalone` or `bench-hybrid` development shells:
    ```sh
    nix develop '.#bench-standalone'
    nix develop '.#bench-hybrid'
    ```

## Code Structure

The repository is organized as follows:

- **`coq-minuska/`**: Contains the Coq sources for Minuska, including the formal semantics and verified components.
- **`minuska/`**: Contains the OCaml sources, including the extracted code and manually written components.
- **`doc/`**: Documentation files, including this guide and other related documents.
- **`bench-standalone/`** and **`bench-hybrid/`**: Scripts and tests for benchmarking the framework.

## Building and Testing

*This section is a placeholder and will be written later.*

## Future Directions

For ideas and missing features, see the [ideas document](./ideas.md).