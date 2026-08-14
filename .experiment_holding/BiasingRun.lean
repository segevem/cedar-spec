import CedarGen.Relational.BiasingTest

/-! Scratch runner: capture the biased generator's slow tail across sizes.
Small `n`, capped `attempts`, low `slowMs` so slow generations are logged (and
flushed) as they happen. -/

#eval biasMeasure 20 8  (attempts := 30) (slowMs := 100)
#eval biasMeasure 20 12 (attempts := 30) (slowMs := 100)
#eval biasMeasure 20 15 (attempts := 30) (slowMs := 100)
