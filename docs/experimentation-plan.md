# Experimentation Plan

The goal of this internship is to see if we can replace (some of) the handwritten Cedar generators with Specimen-derived generators. To do so, we will need to run experiments pitting the generators against each other. Here is a table containing some key differences between Specimen and the Handwritten Generators:

|  | Specimen | Handwritten |
|---|---|---|
| How are choices made? | PRNG with a numeric seed | Parsing from buffer of numbers |
| Overhead | Translated through Protobuf and FFI call from Lean to Rust | Generator and target both in Rust |
| Deterministic? | Only coverage-unguided available, and deterministic per seed | Non-coverage-guided would be deterministic per fixed buffer because we control the one source of randomness, but coverage-guided is effectively nondeterministic because we cannot control the randomness that the fuzzer selects the buffer with. |
| Correctness | Specimen only (excepting soundness bugs) generates inputs valid according to the relational spec, never invalid inputs. | Can create invalid inputs by mixing arbitrary generators with well-formed output generators or by structurally mutating the valid outputs. Capable of producing both valid and invalid inputs. |

## Metrics

To compare generator performance, we will run both generators on the same target T for a time period P repeated R times and measure the following:

- Throughput (average number of tests executed per second)
- 2- and 3-path coverage over time
- Source line coverage over time
- Uniqueness (how often do we generate the same values we generated previously)
- Size (what is the size distribution of the generated values)
- Topmost constructor distribution

## Phased Fuzzing Runs

To measure realistic throughput, we must run the generators as they would be during real testing. We begin each experiment by running the generators with only as much instrumentation as they need to function (none for non-coverage-guided). We run each R times for a fixed time limit and report average throughput and average total tests executed across the runs.

We separate the throughput measurement from the measurements that require further instrumentation to avoid artificially deflating the throughput.

Once we have a measurement of average number of tests ran N, we capture the other metrics by running R repetitions of fuzzing runs that execute N tests each. During these runs, we store the seeds (for unguided Specimen), buffers (for unguided handwritten), or corpus (for coverage-guided handwritten) to an S3 bucket for later analysis.

### Unguided Fuzzers

For unguided fuzzers, the procedure is straightforward:

1. **Throughput phase:** Run R times for a fixed time limit P with no extra instrumentation. Record average throughput and average total tests N.
2. **Collection phase:** Run R repetitions of N tests each, storing the initial seed (Specimen) or buffers (handwritten) and all generated outputs to S3.
3. **Analysis phase:** Replay the stored seeds/buffers against a version of Cedar instrumented with line coverage. Compute all metrics (coverage over time, uniqueness, size distribution, topmost constructor) from the stored data.

Since unguided runs are deterministic per seed/buffer, replaying exactly reproduces the original outputs.

### Coverage-Guided Fuzzers

For coverage-guided fuzzers, guidance is effectively nondeterministic — the same starting buffer will not necessarily lead to the same N inputs. To handle this:

1. **Throughput phase:** Run R times for a fixed time limit P with the fuzzer's internal coverage instrumentation only. Record average throughput and average total tests N.
2. **Collection phase:** Run R repetitions of N tests each, storing every buffer the fuzzer selects to S3 along with the generated outputs.
3. **Analysis phase:** Replay the stored buffers against a line-coverage-instrumented version of Cedar. Compute coverage over time and other metrics from the stored data.

By storing every buffer rather than relying on the corpus alone, we avoid the issue of the corpus being selected by a different coverage criterion than the one we ultimately measure. This ensures we can deterministically reproduce every input for analysis regardless of the nondeterminism of the guidance.

## Measuring Line Coverage

We use LLVM's instrumentation counters (region coverage) during analysis replays. The relatively heavyweight `llvm-cov` tool is used only at the end to map region coverage to source line coverage. Since the analysis phase replays stored inputs rather than running live, the cost of instrumentation does not affect throughput measurements.

## Plotting

We plot the median as a line with a shaded region for the 95% bootstrap confidence interval of the median for coverage and k-paths over time.

## Targets

In terms of targets, we are starting with validation-drt (comparing the Specimen generator against the type-directed and non-type-directed variants) and then adding validation-pbt (type-directed and not), and the symcc-term-drt variants. All of these can be realized with the current Specimen generator (once the full policy generator supporting scope constraints is finished).

Additionally, we will create valid-only variants of the handwritten generator targets by disabling the invalid input generation paths (arbitrary generators, structural mutation). This provides a more direct apples-to-apples comparison with Specimen, which by construction only generates spec-valid inputs. Without this, raw coverage numbers would be misleading: Specimen structurally cannot reach rejection/error-handling paths, so comparing it against a generator that exercises those paths conflates generator quality with generator scope.

The valid-only handwritten variants let us isolate the question "for the space of valid inputs, which generator achieves better coverage?" from the separate question "how much additional coverage does invalid input generation provide?"

## Specimen Variants

We have constructed various scoring and weighting heuristics for Specimen and will run experiments for many of them (some simple ones don't suffice to make a generator for Cedar that terminates in a reasonable amount of time). Additionally, depth of data unconstrained by relations and budget for the generators constrained by relations (like that for well-typed expressions) are parameters to explore.

### Scoring Heuristics

Scoring heuristics rank the quality of derived generation schedules and guide the branch-and-bound search for optimal schedules:

- **DefaultScore** — Sum of (checks, length, unconstrained steps); the original heuristic
- **WorstLeafScore** — Max (not sum) across coverage-trie leaves; penalizes worst-case paths
- **DensityScore** — Categorical density (Total/Partial/Backtracking/Checking) from "Testing Theorems, Fully Automatically"; inverts ordering for checkers/enumerators
- **UniformDensityScore** — Like DensityScore but without inverting ordering for checkers/enumerators
- **GradedUniformDensityScore** — Two-axis check severity (CheckSpeed x PassLikelihood) for finer discrimination among Checking-density schedules
- **BoundedGradedScore** — Refines GradedUniformDensity with a Boundedness field (Finite/Bounded/Unbounded) distinguishing structurally-decreasing recursion from potentially-infinite enumeration
- **InputAwareGradedScore** — Like GradedUniformDensity but penalizes checks whose generated variables overlap with inputs ("generate then verify against input" patterns)
- **SourceQualityScore** — Tracks per-variable source quality across steps; variables from SuchThat carry the dep's density as quality, variables from Unconstrained carry maximum penalty

### Weighting Heuristics

Weighting heuristics control the runtime frequency with which constructors are selected during generation:

- **defaultCtorWeight** — base=1, recursive=numBase*size/numRec; ignores score
- **sizeProportionalCtorWeight** — base=1, recursive=size+1 (the QuickChick strategy); ignores score
- **flatCtorWeight** — every constructor gets weight 1; ignores everything
- **scoreAwareCtorWeight** — boosts good constructors (low badness) and deprioritizes recursive ones with a size-based penalty
- **balancedCtorWeight** (default) — controls aggregate P(recursive) ~ size / (size + 4*numBase) by distributing size across all recursive ctors; base ctors get a 4x boost
- **qualityCtorWeight** — quality-only weight with no structural bias; relies on budget splitting for termination

### Other Parameters

- Depth of data unconstrained by relations
- Budget for the generators constrained by relations (like that for well-typed expressions)

## Execution Plan

### Starting Point: validation-drt

The first experiment compares Specimen against the handwritten type-directed and non-type-directed generators on the validation-drt target. This is the simplest target to get running and gives us the initial throughput and coverage baselines.

Goals for this phase:
1. Get the full phased pipeline working end-to-end (throughput measurement, collection to S3, analysis replay)
2. Establish baseline throughput and line coverage for the handwritten generators (type-directed and non-type-directed)
3. Run Specimen with the default configuration (balancedCtorWeight + DefaultScore) and compare
4. Validate the experimental infrastructure (S3 storage, replay determinism, coverage instrumentation)

### Next Goals

1. **Specimen variant sweep on validation-drt** — Run the full matrix of scoring and weighting heuristic combinations to identify which configurations are competitive
2. **Valid-only handwritten variants** — Disable invalid input generation in the handwritten generators and run on validation-drt for a direct comparison with Specimen on the shared valid-input space
3. **Add validation-pbt target** — Extend experiments to validation-pbt (type-directed and not) to see if results generalize across targets
4. **Add symcc-term-drt target** — Run on the symcc-term-drt variants for a different coverage profile
5. **Coverage-guided handwritten baseline** — Run the guided handwritten fuzzer through the phased pipeline, storing all buffers, to establish the coverage ceiling we are aiming to match with unguided Specimen

## Future Work

### Invalid Input Generation for Specimen

Specimen currently only generates valid inputs by construction. To cover rejection/error-handling paths, we would need a mutator that takes valid Specimen outputs and introduces targeted violations. A naive structural mutator (swap a constructor, delete a subtree, flip a type annotation) risks clustering on a few shallow rejection paths rather than exercising diverse validation logic. A smarter mutator would need awareness of which validity conditions to violate — at which point it approaches a targeted invalid generator. This remains an open problem.

### Guided Specimen

The most direct comparisons we can perform are between the unguided Specimen generator and the unguided handwritten generator, but we also want to measure the guided handwritten fuzzer. Ideally, we would also be able to compare it directly to a guided version of the Specimen generator. To do so, we would need to support buffer-parsing generators in Specimen as well as the current PRNG seed based generators. This can be achieved with the correct Generator monad after we have transitioned Specimen to use Basalt, which allows generators to be parameterized over all types of generators (that satisfy its defining typeclasses).
