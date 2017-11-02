namespace whileSyntax

inductive wExpr : Type
| ident : string → wExpr
| num   : ℕ → wExpr
| add : wExpr → wExpr → wExpr
| mul : wExpr → wExpr → wExpr

namespace wExpr
infixl `+` := add
infixl `*` := mul
end wExpr

inductive wBool : Type
| true  : wBool
| false : wBool
| eq    : wBool → wBool → wBool
| lt    : wBool → wBool → wBool
| and   : wBool → wBool → wBool
| or    : wBool → wBool → wBool
| not   : wBool → wBool → wBool

namespace wBool
infixl `=` := eq
infixl `<` := lt 
precedence `:∧` :1
infixl `:∧` := and
precedence `:∨` :2
infixl `:∨` := or
infixl `¬` := not
end wBool

inductive wComm : Type
| skip       : wComm
| assign     : string → wExpr → wComm
| seq        : wComm → wComm → wComm
| ifThenElse : wBool → wComm → wComm → wComm
| whileDo    : wBool → wComm → wComm

namespace wComm
infixl `:=` := assign
infixl `;` := seq
end wComm

def state := string → ℕ

inductive config : Type 1
| configE : wExpr → state → config
| configB : wBool → state → config
| configC : wComm → state → config

end whileSyntax
