module Point_Eq (E : Eq with type a = float) = struct
  type a = point

  let ( == ) (Pt (p1x, p1y)) (Pt (p2x, p2y)) =
    E.(p1x == p2x) && E.(p2x == p2y)
  ;;
end
