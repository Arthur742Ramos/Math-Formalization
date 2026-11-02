# Vendored proof-source notices

This package retains all 126 Lean modules from the public recursion predecessor at `0d60a72299f83786929a45a29a2ddc2dba921572` byte-for-byte. `CreativeZero.lean` is new. The predecessor includes named executable-encoding validity and inverse proof fields for fixed-definition comparison.

Of the inherited modules, 125 `LambdaTuring/` modules derive from the authors’ public Lean proof checkpoint c695e9a1b47f0c9cb7031f5c13b8494180b7b948. In `FoldCode.lean`, the proof of `validCode_iff` is written explicitly to avoid a module-private generated helper. In `TermCode.lean`, the syntax encoder uses reordered structural equations to avoid a module-dependent generated matcher. In `ExecutableTermCoding.lean`, the validity and inverse proof fields are named to avoid module-dependent generated proof helpers in fixed-definition comparison. Statements and encoding behavior are unchanged. The other 122 inherited modules are byte-for-byte copies of c695e9a; relative to predecessor 236c361f809b2004cde6ecbed679c864bd16ee90, 124 of the 125 inherited modules are unchanged and only `ExecutableTermCoding.lean` is adapted. Original file headers are preserved. The original proof package’s third-party notices follow in full. The earlier Isabelle predecessor was reviewed locally at 6fed1b6e77514ec161a8fd4718fde1587f2cf624; that snapshot is not asserted to be publicly available or identical to the AFP submission.

---

# Third-party and reference notices

`StandardReduction.lean` adapts Isabelle/HOL's `HOL-Proofs-Lambda.Standardization` (author Stefan Berghofer, copyright 2005 TU Muenchen). The Isabelle distribution notice follows.

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

Several CPS, recursion, and head-search proofs follow or adapt the related Isabelle lambda–Turing project by Arthur Freitas Ramos, David Barros Hulak, and Ruy José Guerra Barretto de Queiroz. That project's license follows.

BSD 3-Clause License

Copyright (c) 2026, Arthur Freitas Ramos, David Barros Hulak,
and Ruy José Guerra Barretto de Queiroz.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors
   may be used to endorse or promote products derived from this software
   without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The primitive-recursion argument in `LambdaTuring/ListCodeArithmetic.lean` adapts the `prec` case of `Mathlib/Computability/TuringMachine/Config.lean`, copyright 2020 Mario Carneiro, released under the Apache License 2.0. The Lean file identifies the source and copyright; the original source header is reproduced below.

The square-root recurrence in `LambdaTuring/ListCodeSqrt.lean` adapts the `sqrt` proof in `Mathlib/Computability/Primrec/List.lean`, copyright 2018 Mario Carneiro, released under the Apache License 2.0. The Lean file identifies the source and copyright; the original source header is reproduced below.

The list-code search connection in `LambdaTuring/ListCodeSearch.lean` follows the `rfind` case of `Mathlib/Computability/TuringMachine/Config.lean`, copyright 2020 Mario Carneiro, released under the Apache License 2.0. The Lean file identifies the source and copyright and adds a proof for partial tests; the original source header is reproduced below.

The executable simulator support enumerations in `FiniteExtraction.lean` and `FiniteSupportList.lean` follow the support constructions in `Mathlib/Computability/TuringMachine/StackTuringMachine.lean` and `PostTuringMachine.lean`, copyright 2018 Mario Carneiro, and `ToPartrec.lean`, copyright 2020 Mario Carneiro. These Mathlib sources are released under the Apache License 2.0; the Lean files identify their sources and copyrights, and the original headers are reproduced below.

The finite TM1 state-support enumeration in `TM1FiniteTable.lean` follows `Mathlib/Computability/TuringMachine/PostTuringMachine.lean`, copyright 2018 Mario Carneiro, released under the Apache License 2.0. The Lean file identifies the source and copyright; the original source header is reproduced below.

The original headers of the attributed Mathlib sources at commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` are reproduced here. The 2018 header occurs in `Computability/Primrec/List.lean`, `Computability/TuringMachine/StackTuringMachine.lean`, and `Computability/TuringMachine/PostTuringMachine.lean`:

```text
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
```

The 2020 header occurs in `Computability/TuringMachine/Config.lean` and `Computability/TuringMachine/ToPartrec.lean`:

```text
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
```

The lambda-calculus source files in `LambdaTuring/Upstream` adapt CSLib pull request 475 at commit `cd9bd6ba0537764eb422532400e99b2c90f34256` (https://github.com/leanprover/cslib/pull/475). They retain their source copyright notices for zayn7lie and credit Zayn Wang, with Maksym Radziwill also credited in `DeBruijn.lean`. Those files identify the Apache 2.0 license and their local adaptations in their headers. The pinned source is a pull-request revision, not a claim that the development is part of a released CSLib version.
