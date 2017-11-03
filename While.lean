import .WhileSyntax
open whileSyntax
open whileSyntax.config
open whileSyntax.wExpr
open whileSyntax.wComm
open whileSyntax.wBool

namespace semantics

def smallStep : config → config
| (configE (ident x, state)) := configE (num (state x), state)
| (configE (num a, state)) := configE (num a, state)
| (configE (exp1 + exp2, state)) := let (configE (exp1Eval, _)) := smallStep (configE (exp1, state)) in 
                                      configE (exp1Eval + exp2, state)
| (exp1 * exp2) := smallStepExpr exp1 * smallStepExpr exp2




end semantics