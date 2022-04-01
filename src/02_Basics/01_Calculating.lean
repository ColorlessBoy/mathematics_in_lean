import data.real.basic

/- An example. -/

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c
end

/- Try these.-/

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc b c a,
  rw mul_comm c a
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw mul_comm,
  rw mul_assoc,
  rw mul_comm c a,
end

/- An example. -/

example (a b c : ℝ) : a * b * c = b * c * a :=
begin
  rw mul_assoc,
  rw mul_comm,
end

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/

example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm,
  rw mul_assoc,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw mul_comm,
  rw mul_assoc,
  rw mul_comm a,
end

/- Using facts from the local context. -/

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin
  rw h',
  rw ←mul_assoc,
  rw h,
  rw mul_assoc
end

/- Try these. For the second one, use the theorem `sub_self`. -/

example (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  rw mul_comm,
  rw mul_assoc,
  rw h,
  rw ←mul_comm,
  rw ←mul_assoc,
end

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw mul_comm b a,
  rw ←hyp',
  rw sub_self,
end

/- Examples. -/

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
by rw [h', ←mul_assoc, h, mul_assoc]

section

variables a b c d e f g : ℝ

example (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
by rw [h', ←mul_assoc, h, mul_assoc]

end

section
variables a b c : ℝ

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check @mul_comm
#check two_mul a
#check add_mul
#check mul_add

end

section
variables a b : ℝ

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul]
end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
          by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b :
          by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     :
          by rw [mul_comm b a, ←two_mul]


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      sorry
    end
  ... = a * a + (b * a + a * b) + b * b : by sorry
  ... = a * a + 2 * (a * b) + b * b     : by sorry
end

/- Try these. For the second, use the theorems listed underneath. -/

section
variables a b c d : ℝ

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin
  rw [add_mul, mul_add, mul_add],
  rw ←add_assoc
end

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * (c + d) + b * (c + d): by rw add_mul
  ... = a * c + a * d + (b * c + b * d) : by rw [mul_add, mul_add]
  ... = a * c + a * d + b * c + b * d : by rw [←add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = (a + b) * a - (a + b) * b : by rw [mul_sub]
  ... = a * a + b * a - (a * b + b * b) : by rw [add_mul, add_mul]
  ... = a * a + b * a - a * b - b * b : by rw [← sub_sub]
  ... = a * a + (b * a - a * b) - b * b: by rw [← add_sub (a * a)]
  ... = a * a + (a * b - a * b) - b * b: by rw [mul_comm b a]
  ... = a * a + 0 - b * b: by rw [sub_self (a * b)]
  ... = a * a - b * b: by rw [add_zero]
  ... = a^2 - b^2: by rw [pow_two, pow_two]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

/- Examples. -/

section
variables a b c d : ℝ

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a * d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp
end

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end

end

