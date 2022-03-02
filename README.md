# Architecture to Architecture Mapping Proofs

Proofs for translating memory instructions between different CPU architectures, written in [Agda](https://agda.readthedocs.io/).


## Running/Checking

* [Install Agda (v.2.6.2)](https://agda.readthedocs.io/en/v2.6.2/getting-started/installation.html) with its standard library
* Make sure Agda can find the standard library (see the `~/.agda/libraries` and `~/.agda/defaults` files in the installation instructions)

> :warning: The proofs were developed with standard library version 1.7.1. Other versions may be incompatible.

There are multiple ways of type-checking the proofs; Two are listed below.


### Running/Checking: Command Line

The easiest way of checking the proofs is through a terminal.

* Run `agda src/Main.agda --safe`.

Once a proof type-checks, it's correct. Also check the "Code Navigation" section below to understand *what* it is proving.


### Running/Checking: Emacs

Another way of checking the proofs is with the `agda-mode` in Emacs.

* Install [Emacs](https://www.gnu.org/software/emacs/)
* Install `agda-mode` as described in Agda's install instructions (above).
* Load an `.agda` file in Emacs, and press `C-c C-l` to type-check the file.

If a proof type-checks, it's correct. Also check the "Code Navigation" section below to understand *what* it is proving.


## Code Navigation

The proofs consists of several parts (in `src/`):

* `Main.agda` - Links to all proofs
* `Arch/` - Memory model specifications for architectures
  * `General/` - A general specification of an execution in the axiomatic model. This is instantiated by the individual architectures (below).
  * `Armv8.agda` - The Armv8 model[[1](https://doi.org/10.1145/3158107)]
  * `X86.agda` - The X86 model[[2](https://doi.org/10.1145/2627752)]
  * `LIMM.agda` - Our LIMM model
* `Map*to*.agda` - The *specification* of mapping executions between architectures
* `Transform*.agda` - The *specificaton* of elimination and reordering transformations on LIMM
* `Proof/` - Contains all the proofs (also referenced by `Main.agda`)
  * `Framework.agda` - A general framework for memory model proofs
  * `Mapping/` - The mapping proofs between architectures
    * `Framework.agda` - A framework for architecture-mapping proofs. Extends the general framework
    * `X86toLIMM.agda`
    * `LIMMtoArmv8.agda`
    * `Armv8toLIMM.agda`
    * `LIMMtoX86.agda`
  * `Elimination/` - The elimination proofs
    * `Framework.agda` - A framework for elimination proofs. Extends the general framework
    * `RAR.agda` / `RAW.agda` / `WAW.agda` - Proofs for elimination *without* fences
    * `FRAR.agda` / `FRAW.agda` / `FWAW.agda` - Proofs for eliminations *with* fences
  * `Reorder/` - Reordering proofs (also see the table in `src/TransformReorder.agda`)
    * `Single.agda` - Proves `a ; b  ->  b ; a` (for some `a`,`b`)
    * `Reorder12.agda` - Proves `a ; (b ; c)  ->  (b ; c) ; a` (for some `a`,`b`,`c`)
    * `Reorder21.agda` - Proves `(a ; b) ; c  ->  c ; (a ; b)` (for some `a`,`b`,`c`)

Note that some transformations follow from others. Examples of these are eliminations over *some* fences:

* FRAR (over `F_WW`)
  * `a = X ; F_WW ; b = X` --reorder--> `a = X ; b = X; F_WW` --RAR--> `a = X ; b = a ; F_WW`
* FWAW (over `F_RM`)
  * `X = a ; F_RM ; X = b` --reorder--> `F_RM ; X = a ; X = b` --WAW--> `F_RM ; X = b`
* FRAW (over `F_WW` and `F_RM`)
  * `X = a ; F_WW ; b = X` --reorder--> `X = a ; b = X; F_WW` --RAW--> `X = a ; b = a ; F_WW`
  * `X = a ; F_RM ; b = X` --reorder--> `F_RM ; X = a ; b = X` --RAW--> `F_RM ; X = a ; b = a`


## Proof Intuition

All proofs follow a similar structure, whose intuition I will give here.

When mapping *instructions* from a source program *S* to target program *T*, program *T* must show *no new behavior* w.r.t. program *S*. That is, every behavior of *T* must be also be observable on *S*. Given an execution *X_T* of *T* (which is wellformed and consistent in the target architecture), we produce a corresponding execution *X_S* of *S*. We then show:
* *X_S* relates to *X_T*, by the mapping from *S* to *T*
* The behaviors of *X_S* and *X_T* are equal
* *X_S* is wellformed
* *X_S* is consistent in the source architecture

On terminology, intuitively:
* **Behavior**: The memory state upon termination
* **Wellformed**: Everything "makes sense". E.g., every read event reads-from a single write, all orders are transitive, etc. (See `Wellformed` in `Arch/General/Execution.agda` for details)
* **Consistent**: Satisfies architecture-specific consistency axioms. These enforce the ordering of events in an execution; For instance, the effects of *fences* on ordering. (E.g., see `IsLIMMConsistent` in `Arch/LIMM.agda`)


## References

* [1] Christopher Pulte, Shaked Flur, Will Deacon, Jon French, Susmit Sarkar, and Peter Sewell. 2017. [Simplifying ARM concurrency: multicopy-atomic axiomatic and operational models for ARMv8](https://doi.org/10.1145/3158107).
* [2] Jade Alglave, Luc Maranget, and Michael Tautschnig. 2014. [Herding Cats: Modelling, Simulation, Testing, and Data Mining for Weak Memory](https://doi.org/10.1145/2627752).
