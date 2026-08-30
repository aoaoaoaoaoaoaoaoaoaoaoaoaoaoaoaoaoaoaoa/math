# Local bibliography

Each retained artifact has a same-stem synopsis recording its citation, provenance, digest,
content, and version hazards. A metadata-only synopsis records a source when no redistributable
full text was located.

## Frankl's union-closed sets conjecture

| Key | Status | Role in the investigation |
| --- | --- | --- |
| [Gilmer22](gilmer-2022-constant-lower-bound-union-closed.md) | arXiv v2; CC BY | First dimension-free constant and the entropy-growth engine |
| [Sawin23](sawin-2022-improved-lower-bound-union-closed.md) | arXiv v3; metadata only | Golden-ratio sharpening, dependent coupling, and failure of Gilmer's stronger conjecture |
| [CL22](chase-lovett-2022-approximate-union-closed.md) | arXiv v1; metadata only | Golden-ratio bound and sharp barrier for approximately union-closed families |
| [AHS24](alweiss-huang-sellke-2024-improved-lower-bound-frankl-journal.md) | peer-reviewed EJC; CC BY-ND | Unconditional benchmark `(3 − √5)/2` |
| [Boppana23](boppana-2023-binary-entropy-inequality.md) | arXiv v1; CC BY | Independent analytic proof of the baseline entropy inequality |
| [Yu23](yu-2023-dimension-free-bounds-union-closed-journal.md) | peer-reviewed Entropy; CC BY | Finite coupling optimization and uncertified numerical `0.38234` evaluation |
| [Cambie25](cambie-2022-better-bounds-union-closed.md) | arXiv v2; CC BY | Two-variable reduction and the numerical precursor of the affine wall `0.382345533…` |
| [Liu24](liu-2023-conditionally-iid-coupling-union-closed.md) | peer-reviewed CISS / arXiv; metadata only | Analytic strict-improvement mechanism and conditional `0.382709087…` candidate |
| [Cambie23](cambie-2023-progress-union-closed.md) | peer-reviewed survey; CC BY | Post-breakthrough strategy map and entropy barriers |
| [BruhnSchaudt15](bruhn-schaudt-2015-journey-union-closed.md) | peer-reviewed survey; metadata only | Classical results, failed routes, and exact lattice equivalence |
| [Tian22](tian-2022-height-union-closed.md) | arXiv v2; CC BY | Frankl's conjecture for finite families of height at most three or at least `n−1`; low-height predecessor to Colbert |
| [Colbert26](colbert-2026-chain-conditions-union-closed.md) | peer-reviewed Order; CC BY | Abundant optimal coordinates for union-closed families of chain dimension at most two, including infinite families |
| [Hu23](hu-2023-on-union-closed.md) | peer-reviewed Discrete Math.; metadata only | Minimal-counterexample bounds and historical false-proof warning |
| [Bouchard25](bouchard-2025-lattice-formulation-union-closed.md) | arXiv v1; metadata only | Necessary conditions for a smallest lattice counterexample |
| [CarvalhoMachiavelo25](carvalho-machiavelo-2024-normalized-families-frankl.md) | arXiv v2; metadata only | Normalized-family duality and canonical root-deletion recursion |
| [DasWu25](das-wu-2024-frequent-elements-union-closed.md) | arXiv v3; CC BY | Multiple-frequency theorem and corroboration of the current numerical frontier |
| [vdHRoos26](van-der-hout-roos-2026-frankl-results-conjectures.md) | peer-reviewed JANO; CC BY | 2026 open status and tight-family parity equivalence |
| [LozinZamaraev24](lozin-zamaraev-2024-frankl-horn-functions.md) | peer-reviewed JCTA; CC BY | Horn-function equivalence and class theorems; its stated bidual/self-dual open cases are closed by the audited Karpas density dichotomy |
| [EiterIbarakiMakino99](eiter-ibaraki-makino-1999-bidual-horn-extensions.md) | peer-reviewed Discrete Appl. Math.; metadata only | Structural and algorithmic theory of bidual Horn extensions, including the failure of naive closure-disjointness sufficiency |
| [Karpas17](karpas-2017-two-results-union-closed.md) | arXiv v1; metadata only | Boolean-influence proof of Frankl’s conjecture for union-closed families occupying at least half the cube; directed-influence labels require a documented swap |
| [Gendler25](gendler-2025-union-closed-weighted-cube.md) | arXiv v1; metadata only | Product-measure generalization of Karpas’s half-cube theorem and an independent sign-consistent reconstruction |
| [DeFranco26](defranco-2026-boolean-polynomials-union-closed.md) | arXiv v1; CC BY | Boolean-polynomial encoding; sole located forward citation of the 2024 Horn paper and negative evidence for the bidual-Horn priority check |
| [Bhasin24](bhasin-2024-cubical-complements-union-closed.md) | arXiv v1; CC BY | Cubical complex of simply rooted families; the audit upgrades acyclicity to contractibility and documents three local source defects |
| [Zargar23](zargar-2023-union-closed-nonuniform-distributions.md) | arXiv v2; CC BY | Nilpotent/group semigroup lift; its `k=2,m=1` seam is closed in the binary-kernel audit, yielding weighted Frankl at `t=1/2` |

The constants `0.38234`, `0.382345533…`, and `0.382709087…` have different epistemic
status. Yu's and Cambie's published values depend on uncertified global numerical minimization;
Liu's larger value additionally assumes an infinite-kernel PSD statement and an optimizer-shape
hypothesis. AHS remains the last explicit benchmark supported by an external published proof.
The present repository separately proves and kernel-checks
`38234553336670271/10^17=0.38234553336670271`. Its independent affine-wall audit corrects
Cambie's final reported digits and places the two-coupling obstruction less than `1.2×10⁻¹⁷`
above the formal target; that exact real wall is not a Lean theorem.

## Matrix mortality

| Key | Status | Role in the matrix-mortality investigation |
| --- | --- | --- |
| [CHHN14](cassaigne-halava-harju-nicolas-2014-matrix-mortality.md) | arXiv v3; established paper | Previous antichains, ternary encoding, rank-one scalar-to-mortality reduction, and the neighboring `Z₅(3)` and `M₅(4)` bounds |
| [HHH07](halava-harju-hirvensalo-2007-claus-instances.md) | peer-reviewed IJFCS 2007 | Closest prior art: forced-endpoint absorption into a rank-one idempotent |
| [Neary13](neary-2013-four-pair-pcp-superseded-claim.md) | one-version technical report; claim not retained | Historical five-matrix claim based on a claimed four-pair PCP construction |
| [Neary15](neary-2015-five-pair-pcp.md) | peer-reviewed STACS 2015 | Lemma 9 restricted-tag universality and exact four ordinary pairs; terminal converse audited as defective |
| [CM63](cocke-minsky-1963-tag-universality-memo.md) | MIT AI memo; published in JACM 1964 | Universality at deletion width two with a state-dependent, nonbinary alphabet |
| [DeMol10](de-mol-2010-binary-two-tag-decidability.md) | peer-reviewed Fundamenta Informaticae 2010; author manuscript | Decidability of binary deletion-width-two tag systems and the adjacent width-three frontier |
| [DeMol11](de-mol-2011-simple-tag-systems.md) | peer-reviewed TCS 2011; author manuscript | Experimental and structural status of binary deletion-width-three tag systems |
| [Kurilenko22](kurilenko-2022-post-tag-growth.md) | peer-reviewed Complex Systems 2022; arXiv copy | Unbounded growth in Post's width-three system; no universality or reachability decision theorem |
| [FS23](fazekas-seki-2023-freezing-one-tag-states.md) | peer-reviewed AFL 2023 / EPTCS; CC-BY | Definition of one-tag systems with states and the exact source-model seam; no binary two-state universality bound |
| [Moss08](moss-2008-confusion-memory.md) | peer-reviewed IPL 2008; author-posted manuscript | Binary single-queue halting is Σ₁-complete with unrestricted program control; the construction does not bound states or dequeue on every step |
| [Pierce11](pierce-2011-iterated-length-preserving-transducers.md) | unpublished CMU senior thesis; institutional copy | Reset and binary-toggle iterated transducers support RE-hard safety problems, but the two constructions spend respectively a large alphabet and unrestricted finite control |
| [BPS19](bell-potapov-semukhin-2019-mortality-problem.md) | MFCS 2019; journal 2021 | Independent post-correction statement of the six-generator `3 × 3` bound |
| [Bacik25](bacik-2025-order-four-skolem.md) | peer-reviewed TheoretiCS 2025; CC-BY | Decidability of the algebraic Skolem problem through order four; definitive low-order boundary used by the `M₃(2)` rank census |
| [Michels14](michels-2014-zsigmondy-theorem.md) | revised author exposition; not peer reviewed | Elementary proof of Zsigmondy’s primitive-prime-divisor theorem, including the `2⁶−1` and power-of-two exceptions |
| [HKPY24](hirvensalo-kawamura-potapov-yuyama-2024-linear-recurrence-automata.md) | peer-reviewed RP 2024; author accepted manuscript | Recurrence-controlled reachability vocabulary adjacent to the variable-index `Mₙ = VAⁿU` return problem |
| [ABY10](avila-bochi-yoccoz-2010-uniform-hyperbolicity.md) | peer-reviewed CMH 2010; metadata-only local record | Uniform hyperbolicity of finite `SL₂(ℝ)` cocycles is equivalent to strict invariant multicones, including Markov constraints; component boundaries have bounded periodic `±I`, parabolic, or heteroclinic witnesses |
| [BGT10](bell-ghioca-tucker-2010-dynamical-mordell-lang.md) | peer-reviewed AJM 2010; metadata-only local record | Étale single-map orbit intersections with subvarieties have eventually periodic hitting times, proved by `p`-adic analytic interpolation |
| [JK20](jaax-kiefer-2020-affine-reachability.md) | peer-reviewed MFCS 2020; CC-BY | PSPACE-completeness for integer affine-register reachability, NP-completeness for determinant-`{1,0}` `2 × 2` mortality, and exact affine/upper-triangular reductions |
| [LOPW24](lefaucheux-ouaknine-purser-worrell-2024-porous-invariants.md) | peer-reviewed FMSD 2024; CC-BY | Strongest lattice invariants for multipath integer systems, semilinear separators in decidable strata, and an undecidability boundary for nondeterministic semilinear invariant synthesis |
| [Protasov26v2](protasov-2026-perron-matrix-semigroups-v2.md) | arXiv v2 preprint; CC BY-NC-SA | Whole-semigroup Perron spectra force common invariant cones under irreducibility and low index; dimensions at most four are classified |
| [BB02](bournez-branicky-2002-low-dimensional-mortality.md) | peer-reviewed Theory Comput. Syst. 2002 | Decidability of two rational `2 × 2` generators and the rank-one-endpoint normal form |
| [Dong23](dong-2023-semigroup-algorithms-survey.md) | peer-reviewed survey | Later matrix-semigroup context; no sharper bounded-generator result |
| [Heckman19](heckman-2019-2x2-mortality-invertible.md) | arXiv v1 preprint | Decidability with at most one nonsingular `2 × 2` generator; singular-generator count reduction |
| [NR08](nuccio-rodaro-2008-2x2-mortality-slides.md) | SOFSEM 2008 author slides; paper peer-reviewed | Original decidability result for singular plus unimodular `2 × 2` integer generators |
| [PS17](potapov-semukhin-2017-gl2z-singular-membership.md) | peer-reviewed MFCS 2017; CC-BY | Membership, hence mortality, decidable for singular plus unimodular `2 × 2` integer generators |
| [PS17b](potapov-semukhin-2017-nonsingular-2x2-membership.md) | peer-reviewed SODA 2017; author copy | Membership decidable for arbitrary nonsingular `2 × 2` integer generators; determinant-growth machinery |
| [PS19](potapov-semukhin-2018-vector-scalar-reachability.md) | peer-reviewed JCSS 2019; metadata-only local record | Vector, scalar, and fractional-linear point reachability are decidable in `SL₂(ℤ)`, including regular constraints, through canonical modular-group languages |
| [COSW19](colcombet-ouaknine-semukhin-worrell-2019-low-dimensional-reachability.md) | peer-reviewed ICALP 2019; CC-BY | Half-space reachability in `GL₂(ℤ)` and membership and half-space reachability in rational Heisenberg groups are decidable |
| [DPS24v6](diekert-potapov-semukhin-2024-flat-rational-subsets.md) | arXiv v6 preprint; metadata-only local record | Bounded-alternation rational subsets of `GL₂(ℚ)` admit membership and Boolean-emptiness algorithms; unrestricted rational alternation remains outside the theorem |
| [CCZ20](cadilhac-chistikov-zetzsche-2020-baumslag-solitar.md) | peer-reviewed ICALP 2020; CC-BY | Rational subsets of `BS(1,q)` have effective pointed-expansion automata and PSPACE-complete membership |
| [BKP18](bournez-kurganskyy-potapov-2018-piecewise-affine-reachability.md) | peer-reviewed IJFCS 2018; author accepted manuscript | `p`-adic denominator-weight method for cooriented slopes on bounded intervals |
| [Carelli26](carelli-2026-loop-termination-generalized-collatz.md) | peer-reviewed ICALP 2026; CC BY 4.0 | One-variable loop termination conditional on weak Collatz residue reachability; the residue conjecture holds at modulus two but does not decide mixed-slope point reachability |
| [DP26](dhiman-pandey-2026-collatz-reachability-nondefinability.md) | arXiv v2 preprint; CC BY 4.0 | Full generalized-Collatz reachability is not synchronously base-`q` recognizable for `q+d` a power of two; this does not imply undecidability or exclude stronger and annotated models |
| [LS11](lohrey-steinberg-2009-tilings-submonoids-metabelian.md) | peer-reviewed Theory Comput. Syst. 2011; arXiv v1 | Tiling-based fixed submonoid and rational-subset undecidability in free-module metabelian and two-dimensional lamplighter groups; the free-module hypothesis excludes direct transfer to `ℤ[1/6]⋊ℤ²` |
| [CN12](cassaigne-nicolas-2012-semigroup-freeness.md) | peer-reviewed RAIRO 2012; NUMDAM journal PDF | Explicit nonfree identity for the `(2/3,3/5)` affine benchmark, yielding a length-thirteen guarded shell rewrite |
| [DS25](dong-shafrir-2025-s-unit-equations.md) | arXiv v2 preprint; CC BY | Arbitrary-prime module `S`-unit equations lead to open linear-exponential systems; scope warning, not benchmark hardness |
| [CVZ19](capuano-veneziano-zannier-2019-adic-periodicity.md) | peer-reviewed Math. Comp. 2019; arXiv v2 | Effective sign-and-height classification of rational and quadratic Ruban continued fractions |
| [CMT22](capuano-murru-terracini-2022-adic-finiteness-number-fields.md) | peer-reviewed BSMF 2022; postpublication arXiv v2 | Adelic continuant criterion: `ν≤1` gives finite-or-periodic expansions and `ν<1` gives finiteness |
| [CCMT26](capuano-checcoli-mula-terracini-2026-extraneous-denominators.md) | peer-reviewed Annali 2026; CC BY 4.0 | Extends the adelic finiteness criterion to a fixed finite set of extraneous denominator places |
| [Yas25](yasutomi-2025-simultaneous-real-adic-continued-fractions.md) | peer-reviewed FAM 2025; arXiv v1 | Simultaneous real and p-adic selection with rational termination and two-place approximation bounds |
| [MRS23](murru-romeo-santilli-2023-convergence-adic-continued-fractions.md) | peer-reviewed RNT 2023; CC BY 4.0 | Valuation convergence criteria and a three-phase rational algorithm with blockwise descent |
| [Panti20](panti-2020-decreasing-height-continued-fractions.md) | peer-reviewed ETDS 2020; arXiv v2 | Positive unimodular matrices and complete symbolic blocks that force strict Weil-height descent |
| [WD24](wang-deng-2024-new-adic-continued-fractions.md) | arXiv v2 preprint | Finite-phase p-adic selectors with bounded-block denominator contraction on rational inputs |
| [RS25](romeo-salvatori-2025-adic-continued-fraction-arithmetic.md) | arXiv v1 preprint | Algorithms and obstructions for transporting p-adic continued fractions through Möbius maps |
| [GLNP17](glasby-lubeck-niemeyer-praeger-2017-primitive-cyclotomic.md) | peer-reviewed J. Aust. Math. Soc. 2017; arXiv v4 | Exact strong primitive part of cyclotomic values, retaining full prime-power multiplicity |
| [BE17](bugeaud-evertse-2017-s-parts-recurrences.md) | peer-reviewed Mathematika 2017; arXiv v1 | Effective and asymptotic power-saving bounds for fixed-prime parts of nondegenerate recurrences |
| [BEG18](bugeaud-evertse-gyory-2018-s-parts-forms.md) | peer-reviewed Acta Arith. 2018; arXiv artifact | Effective fixed-`S` power savings for polynomial, binary-form, and decomposable-form values |
| [GW20](grieve-wang-2020-moving-gcd.md) | peer-reviewed Trans. AMS 2020; postpublication arXiv v2 | Moving-target gcd dichotomy for fixed-rank S-unit points with slow coefficient growth |
| [ESS02](evertse-schlickewei-schmidt-2002-multiplicative-linear-equations.md) | peer-reviewed Annals 2002; postpublication arXiv copy | Uniform bound for nondegenerate bounded-term linear equations in finite-rank multiplicative groups |
| [EG13](evertse-gyory-2013-effective-unit-equations.md) | peer-reviewed MPCPS 2013; metadata only | Effective enumeration of two-variable unit equations over finitely generated characteristic-zero domains and effective exponent bounds |
| [Nicolas08](nicolas-2008-gpcp-semi-thue.md) | arXiv v5 lecture notes | Definition and old open/undecidable bounds for bounded GPCP; fixes the four-generator counting convention |
| [HH11](halava-holub-2011-binary-gpcp-reduction-tree.md) | peer-reviewed IJFCS 2011 | Reduction-tree and end-block structure at the decidable `GPCP(2)` endpoint; source-compression machinery |
| [HHH99](halava-harju-hirvensalo-1999-marked-gpcp.md) | FCT 1999 author technical report; journal 2000 | Decidability of GPCP for marked morphisms; excludes marked three-letter source proposals |
| [HH01](halava-harju-2001-pcp-modifications.md) | TUCS report; Bulletin EATCS 2001 | Survey of marked PCP/GPCP and the binary-source decidability mechanism |
| [Holub03](holub-2012-binary-equality-sets.md) | revised author version of Journal of Algebra 2003 | Binary non-periodic equality sets have rank at most two; published-lemma correction documented |
| [Hadravová11](hadravova-2011-binary-equality-length-bound.md) | peer-reviewed; metadata only | Binary equality-word bounds and the historical ternary equality-set frontier |
| [MS05](matiyasevich-senizergues-2005-few-rule-semi-thue.md) | peer-reviewed TCS 2005; metadata only | Three-rule accessibility undecidability; Nicolas's source for the `GPCP(5)` lower bound |
| [Carvalho26](carvalho-2026-free-group-pcp.md) | arXiv v2 preprint | Inverse-transducer queue deletion, all-path converse, and the derived globally shared exponent character and exponent-one equalizer slice |
| [GCL25](guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md) | peer-reviewed LICS 2025; metadata only | Ackermannian reachability and related decision procedures for vector addition systems with nested initial-segment zero tests |
| [CL20](ciobanu-logan-2020-pcp-equalisers.md) | peer-reviewed ICALP 2020; CC-BY | Decidable equalizers for marked monoid morphisms and free-group immersions |
| [CL21](ciobanu-logan-2021-free-group-pcp-variations.md) | peer-reviewed DLT 2021; author manuscript | Relations among free-group PCP, fixed-boundary GPCP, rational constraints, and rank/basis computation, with exact source-rank overheads |
| [Logan22](logan-2022-equalizer-rank-two.md) | peer-reviewed QJM 2022; CC-BY | Equalizers from `F₂` have rank at most two when an input map is injective; basis computation is proved only under retract-image hypotheses |
| [MNU14](myasnikov-nikolaev-ushakov-2013-pcp-groups.md) | peer-reviewed J. Group Theory 2014; arXiv copy | Group PCP/GPCP formulations; warns against transferring group-rank counts to positive monoids |
| [JingEtAl13](jing-gao-gao-gong-li-shao-zhang-2013-minimum-rank-three.md) | arXiv precursor to LAA 2018 | Rank-three zero patterns as projective point-line incidence; rational-real field hazard |
| [Kiefer20](kiefer-2020-weighted-automata-minimization.md) | arXiv expository notes | Exact Hankel rank equals minimum weighted-automaton dimension; no same-zero lower bound |
| [BS21](bell-smertnig-2021-noncommutative-polya.md) | peer-reviewed Selecta 2021; CC-BY | Rational series with coefficients in a finitely generated multiplicative group are exactly unambiguous rational series, via unit equations and linear hulls |
| [VY18](villagra-yakaryilmaz-2016-affine-automata.md) | peer-reviewed Natural Computing 2018; arXiv copy | Affine-automaton zero/nonzero succinctness and its nonlinear measurement seam |
| [SYS19](salehi-yakaryilmaz-say-2019-vector-homing-automata.md) | peer-reviewed IJFCS 2019; arXiv copy | Two-state finite word separation and homing-vector connections to matrix products |
| [YS10](yakaryilmaz-say-2010-nondeterministic-quantum-automata.md) | peer-reviewed QIC 2010; arXiv copy | Exclusive stochastic languages and the gap between zero semantics and integer scalar series |
| [DW16](diekert-walter-2016-synchronization-delay.md) | peer-reviewed ICALP 2016; arXiv copy | Prefix codes of bounded synchronization delay; code theory without full-monoid soundness |
| [Rote24](rote-2024-fixed-pfa-emptiness-full-version.md) | arXiv full version | Longer version of Rote's terminal-pair repair and uniqueness discussion |
| [Rote25](rote-2025-fixed-pfa-emptiness.md) | peer-reviewed MFCS 2025 | Published diagnosis of Neary's terminal flaw and long-block proposal; motivation, no longer a proof dependency |
| [FHS18](forster-heiter-smolka-2018-pcp-reductions-coq.md) | peer-reviewed ITP 2018; Coq artifact | Certified generic TM-to-PCP reduction chain and proof-engineering precedent; does not preserve a four-generator source bound |

Retrieval dates and hashes describe the exact local files, not an abstract work that may have
other versions.
