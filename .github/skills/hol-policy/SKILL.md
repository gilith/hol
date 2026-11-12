---
name: hol-policy
description: "HOL repository guide: use when working with HOL Haskell modules, OpenTheory, the hol package, builds, or tests."
---

# hol-policy Skill: HOL Repository Guidelines

## Repository Overview

The **hol** repository (`gilith/hol`) is a Haskell library implementing a higher-order logic kernel with OpenTheory format support. It reads proof files and provides a pretty-printer compatible with the OpenTheory standard theory library.

- **Language**: Haskell
- **Build System**: Cabal
- **License**: MIT
- **Repository**: https://github.com/gilith/hol

## Repository Organization

### Directory Structure

```
hol/
├── src/               # Library and executable source code
├── test/              # Test data files (article, theory, interface files)
├── doc/               # Documentation files (axioms, boolean logic)
├── dist-newstyle/     # Cabal build output (generated, ignored)
├── hol.cabal          # Cabal package manifest
├── README.md          # Main documentation
└── Setup.hs           # Cabal setup script
```

### Source Code Layout (`src/`)

All Haskell source code is in the `src/` directory organized under a `HOL` module hierarchy:

**Core Modules**:
- `HOL.Syntax` - Higher-order logic syntax
- `HOL.Term` - Term data structures and operations
- `HOL.Type` - Type system
- `HOL.Thm` - Theorem representation
- `HOL.Rule` - Proof rules
- `HOL.Theory` - Theory management
- `HOL.Var` - Variable handling
- `HOL.TypeVar`, `HOL.TypeOp` - Type variables and type operators
- `HOL.Const` - Constants
- `HOL.Conv` - Conversions
- `HOL.Subst`, `HOL.TypeSubst` - Substitution operations

**Data Modules**:
- `HOL.Data` - Core data type definitions
- `HOL.TermData` - Term-specific data structures
- `HOL.TypeData` - Type-specific data structures

**OpenTheory Support**:
- `HOL.OpenTheory` - Main OpenTheory interface
- `HOL.OpenTheory.Article` - Article file parsing
- `HOL.OpenTheory.Interpret` - Interpretation engine
- `HOL.OpenTheory.Package` - Package handling

**Other Modules**:
- `HOL.Print` - Pretty-printing
- `HOL.Parse` - Parsing utilities
- `HOL.Tptp` - TPTP format support
- `HOL.Name` - Name management
- `HOL.Util` - Utility functions

### Executables and Entry Points

#### `hol-pkg` (Main Executable)

Located in `src/Main.hs`

**Purpose**: Read and process proof files in OpenTheory format, outputting theorems and symbols.

**Usage**:
```bash
cabal install --enable-tests
hol-pkg INPUT
```

**Input Formats**:
- `FILE.art` - Proof article file
- `FILE.thy` - Theory package file
- `NAME-VERSION` - Specific version of installed theory package
- `NAME ...` - Latest version of a list of packages

**Example**:
```bash
hol-pkg unit
# Outputs type operators, constants, and 5 theorems for the unit package
```

**Compilation Options** (from hol.cabal):
```
ghc-options: -Wall -threaded "-with-rtsopts=-N" -rtsopts
```

#### Test Suite (`hol-test`)

Located in `src/Test.hs`

**Purpose**: QuickCheck-based property testing and regression testing against OpenTheory files.

**Test Data** (in `test/`):
- `bool.art` - Boolean logic article file
- `bool-def.art` - Boolean definition article
- `bool.thy` - Theory package file
- `bool.int` - Interface file

**Running Tests**:
```bash
cabal test
```

**Test Framework**: QuickCheck 2.4+

## Code Style Conventions

### Module Headers

All modules use a consistent header format with Haddock documentation:

```haskell
{- |
module: $Header$
description: [Brief description]
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module HOL.ModuleName
where
```

**Key Elements**:
- Opening with `{- |` for Haddock documentation
- `module:` field with `$Header$` placeholder
- `description:` field with module purpose
- `license: MIT`
- `maintainer` and `stability` metadata
- `portability: portable` flag

### Imports Organization

Imports follow this pattern:

1. Standard library imports (unqualified or specific)
2. Qualified imports from other HOL modules
3. Qualified imports from external libraries

**Example**:
```haskell
import Control.Monad (guard)
import Data.Maybe (isJust)

import qualified HOL.Const as Const
import HOL.Data (Const,Term,Type,TypeOp,Var)
import qualified HOL.Term as Term
import qualified HOL.Type as Type
```

### Naming Conventions

- **Modules**: CamelCase with dots (e.g., `HOL.Syntax`, `HOL.OpenTheory.Article`)
- **Type names**: CamelCase (e.g., `Term`, `Type`, `Theory`)
- **Functions**: camelCase (e.g., `readArticle`, `mkUnsafe1`)
- **Type operators**: Use qualified imports with short aliases (e.g., `Map`, `Set`)

### Code Organization

Modules typically organize code into logical sections separated by comments:

```haskell
-------------------------------------------------------------------------------
-- Section Name
-------------------------------------------------------------------------------
```

### GHC Compilation Flags

**Library**:
```
ghc-options: -Wall
```

**Executable**:
```
ghc-options: -Wall -threaded "-with-rtsopts=-N" -rtsopts
```

**Test Suite**:
```
ghc-options: -Wall
```

The `-Wall` flag enables all warnings; libraries are built with standard warnings only.

## Build and Test Workflow

### Installation

```bash
git clone https://github.com/gilith/hol.git
cd hol
cabal install --enable-tests
```

### Running Tests

```bash
cabal test
```

The test suite uses QuickCheck for property-based testing and reads OpenTheory files from the `test/` directory.

### Building Documentation

The README.md is the primary documentation. The `doc/` directory contains supplementary files (axioms, boolean logic reference).

### Profiling (Advanced)

The project supports CPU and memory profiling:

1. Ensure GHC profiling libraries are installed
2. Configure with profiling:
   ```bash
   cabal configure --enable-library-profiling --enable-profiling --enable-benchmarks
   cabal install --only-dependencies --enable-library-profiling
   ```
3. Build and run benchmarks:
   ```bash
   cabal build
   cabal bench
   ```
4. Analyze profiles with `less hol-profile.prof` or generate PDF with `hp2ps` and `ps2pdf`

## Dependency Management

### Core Dependencies

From `hol.cabal`:
- `base >= 4.0 && < 5.0` - Standard Haskell base library
- `bytestring >= 0.9` - Efficient byte sequences
- `containers >= 0.5` - Data structures (Map, Set)
- `filepath >= 1.3` - File path utilities
- `parsec >= 3.1` - Parser combinator library
- `pretty >= 1.1` - Pretty-printing
- `process >= 1.2` - Process management
- `text >= 0.11` - Text strings
- `transformers >= 0.3` - Monad transformers

### Test Dependencies

- `QuickCheck >= 2.4` - Property-based testing framework

## Testing Strategy

- **Type**: Property-based testing using QuickCheck
- **Entry Point**: `src/Test.hs` (Main module for test suite)
- **Test Data**: OpenTheory files in `test/` directory
- **Regression**: Tests verify parsing and interpretation of reference files (bool.art, bool-def.art, etc.)

## Cabal Project Configuration

### Files

- `hol.cabal` - Main package manifest
- `Setup.hs` - Cabal setup script
- `cabal.project.local` - Local project overrides (ignored by git)

### Default Language

- `Haskell2010` - All components use Haskell2010 standard

## Version

Current version: **1.4**

## Maintenance

- **Author/Maintainer**: Joe Leslie-Hurd <joe@gilith.com>
- **License**: MIT
- **Stability**: Provisional (as per module metadata)
- **Portability**: Portable across Haskell platforms
