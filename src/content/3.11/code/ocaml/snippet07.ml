module type Exp = sig
  type a
  type b
  type 'a d = I of 'a
  type 'a k = 'a * a

  include
    Lan with type 'a k := a * 'a and type 'a d := 'a d and type a := b
end
