
(* Strict equality on nodes *)

(** Equality functions on nodes. *)
let id_v_nodes : v_node -> v_node -> bool = fun n1 n2 -> n1 == n2 ||
  let eq_expr e1 e2 = eq_expr ~strict:true e1 e2 in
  let eq_bndr b1 b2 = eq_bndr ~strict:true b1 b2 in
  match (n1, n2) with
  | (VN_LAbs(b1)   , VN_LAbs(b2)   ) -> eq_bndr V b1 b2
  | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> c1.elt = c2.elt && p1 = p2
  | (VN_Reco(m1)   , VN_Reco(m2)   ) -> M.equal (=) m1 m2
  | (VN_Scis       , VN_Scis       ) -> true
  | (VN_VWit(w1)   , VN_VWit(w2)   ) -> let (f1,a1,b1) = w1 in
                                        let (f2,a2,b2) = w2 in
                                        eq_bndr V f1 f2 && eq_expr a1 a2 &&
                                        eq_expr b1 b2
  | (VN_UWit(t1,b1), VN_UWit(t2,b2)) -> eq_expr t1 t2 && eq_bndr V b1 b2
  | (VN_EWit(t1,b1), VN_EWit(t2,b2)) -> eq_expr t1 t2 && eq_bndr V b1 b2
  | (VN_ITag(n1)   , VN_ITag(n2)   ) -> n1 = n2
  | (_             , _             ) -> false

let id_t_nodes : t_node -> t_node -> bool = fun n1 n2 -> n1 == n2 ||
  let eq_expr e1 e2 = eq_expr ~strict:true e1 e2 in
  let eq_bndr b1 b2 = eq_bndr ~strict:true b1 b2 in
  match (n1, n2) with
  | (TN_Valu(p1)     , TN_Valu(p2)     ) -> p1 = p2
  | (TN_Appl(p11,p12), TN_Appl(p21,p22)) -> p11 = p21 && p12 = p22
  | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> eq_bndr S b1 b2
  | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> eq_expr s1 s2 && p1 = p2
  | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> p1 = p2 && l1.elt = l2.elt
  | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> p1 = p2 && M.equal(eq_bndr V) m1 m2
  | (TN_FixY(p11,p12), TN_FixY(p21,p22)) -> p11 = p21 && p12 = p22
  | (TN_UWit(t1,b1)  , TN_UWit(t2,b2)  ) -> eq_expr t1 t2 && eq_bndr T b1 b2
  | (TN_EWit(t1,b1)  , TN_EWit(t2,b2)  ) -> eq_expr t1 t2 && eq_bndr T b1 b2
  | (TN_ITag(n1)     , TN_ITag(n2)     ) -> n1 = n2
  | (_               , _               ) -> false
