import .WhileSyntax
open whileSyntax
open whileSyntax.configExpr
open whileSyntax.wExpr
open whileSyntax.wComm
open whileSyntax.wBool

namespace semantics

def a := num 1
def b := num 2
def c := num 3
def d := ident("x")
def f : string → ℕ
| "x" := 4
| _   := 0
def exampleConfig := (configE(a + b + (c * d), f))


def oneSmallStepExpr : configExpr → configExpr
| (configE (num a, state)) := configE (num a, state)
| (configE (ident x, state)) := configE (num (state x), state)
| (configE (num a + num b, state)) := configE (num (a + b), state)
| (configE (num a * num b, state)) := configE (num (a * b), state)
| (configE (num a + exp2, state)) := let (configE (exp2', state')) := oneSmallStepExpr (configE (exp2, state)) in
                                       configE (num a + exp2', state')
| (configE (num a * exp2, state)) := let (configE (exp2', state')) := oneSmallStepExpr (configE (exp2, state)) in
                                       configE (num a * exp2', state')
| (configE (exp1 + exp2, state)) := let (configE (exp1', state')) := oneSmallStepExpr (configE (exp1, state)) in 
                                      configE (exp1' + exp2, state')
| (configE (exp1 * exp2, state)) := let (configE (exp1', state')) := oneSmallStepExpr (configE (exp1, state)) in 
                                      configE (exp1' * exp2, state')

def smallStepExpr : configExpr → configExpr
| (configE (num a, state)) := configE (num a, state)
| a := have sizeof (oneSmallStepExpr a) < sizeof a, from sorry,
       smallStepExpr $ oneSmallStepExpr a

def bigStepExpr : configExpr → configExpr
| (configE (num a, state)) := configE (num a, state)
| (configE (ident x, state)) := configE (num (state x), state)
| (configE (num a + num b, state)) := configE (num (a + b), state)
| (configE (num a * num b, state)) := configE (num (a * b), state)
| (configE (exp1 + exp2, state)) := let (configE (exp1', state')) := bigStepExpr (configE (exp1, state)),
                                        (configE (exp2', state'')) := bigStepExpr (configE (exp2, state')) in
                                      have sizeof exp2' + sizeof exp1' < sizeof exp2 + sizeof exp1, from sorry,
                                      bigStepExpr $ configE (exp1' + exp2', state'')
| (configE (exp1 * exp2, state)) := let (configE (exp1', state')) := bigStepExpr (configE (exp1, state)),
                                        (configE (exp2', state'')) := bigStepExpr (configE (exp2, state')) in
                                      have sizeof exp2' * sizeof exp1' < sizeof exp2 * sizeof exp1, from sorry,
                                      bigStepExpr $ configE (exp1' * exp2', state'')

theorem normal_forms (e : configExpr) : (∃ n : ℕ, ∃ f : string → ℕ, smallStepExpr e = configE (num n, f) ) :=
begin
admit
end

def g := let (configE (a, _)) := smallStepExpr (configE (num 7 + num 6, f)) in a
def h := let (configE (a, _)) := bigStepExpr (configE (num 7 + ident "x", f)) in a
def i := let (configE (a, _)) := bigStepExpr exampleConfig in a
def j := let (configE (a, _)) := smallStepExpr exampleConfig in a

#eval i
#eval j


end semantics