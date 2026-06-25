import Inhabit.Resolution

-- Inferences
def trivial_inf : Inference := ⟨[], .top⟩

theorem trivial_sound : trivial_inf.sound := by
  intros s i h
  trivial

def contra_inf : Inference := ⟨[.btm], .var "p"⟩

theorem contra_sound : contra_inf.sound := by
  intros s i h
  simp [contra_inf] at h

def modpon_inf : Inference := ⟨[.var "p", .imp (.var "p") (.var "q")], .var "q"⟩

theorem modpon_sound : modpon_inf.sound := by
  intros i h
  simp_all [modpon_inf]
