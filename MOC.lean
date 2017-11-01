namespace hidden

inductive exp : Type
| num : ℕ → exp
| add : exp → exp → exp

namespace exp

infixl `+` := add

def output : exp → ℕ
| (num x) := x
| (exp1 + exp2) := output exp1 + output exp2

theorem normalForms (e : exp) : (∃ x : ℕ, output e = x) :=
begin

induction e,

-- Base case
case num a 
{ have h : output (num a) = a, by refl,
  exact (exists.intro a h) 
},

-- Recursive case
case add exp1 exp2
{ have h_add : output (exp1 + exp2) = output exp1 + output exp2, by refl,
  have inductive_step : ∃ x : ℕ, output exp1 + output exp2 = x,
  from 
    match ih_1, ih_2 with
      ⟨y, exp1_norm⟩, ⟨z, exp2_norm⟩ := ⟨(y + z), by rw [exp1_norm, exp2_norm]⟩
    end,
  exact (exists.intro (output (exp1 + exp2)) (h_add)) 
},

end

end exp
end hidden