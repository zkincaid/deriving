open Tests_defs

open Deriving_Compare

let sum =
  begin
    assert (0 = Compare_sum.compare S0 S0);
    assert (not (0 = Compare_sum.compare S0 (S1 0)));
    assert (0 = Compare_sum.compare (S1 0) (S1 0));
    assert (0 = Compare_sum.compare (Stup (3,0.0)) (Stup (3,0.0)));
    assert (not (0 = Compare_sum.compare (Stup (0,0.0)) (Stup (1,0.0))));
    assert (Compare_sum.compare S0 (S1 0) > 0);
    assert (Compare_sum.compare (S1 0) S0 < 0);
    assert (Compare_sum.compare (S1 0) (S1 1) < 0);
    assert (Compare_sum.compare (S1 1) (S1 0) > 0);
    assert (Compare_sum.compare (S2 (0, 0.0)) (S2 (0, 0.1)) < 0);
    assert (Compare_sum.compare (S2 (0, 0.0)) (S2 (0, -0.1)) > 0);
    assert (Compare_sum.compare (S2 (0, 0.0)) (S2 (1, -0.1)) < 0);
  end

let nullsum =
  begin
    assert (0 = Compare_nullsum.compare N2 N2)
  end

let r1 = 
  begin
    assert (0 = Compare_r1.compare
              { r1_l1 = 10; r1_l2 = 20 }
              { r1_l1 = 10; r1_l2 = 20 });
    assert (not (0 = Compare_r1.compare
                   { r1_l1 = 20; r1_l2 = 10 }
                   { r1_l1 = 10; r1_l2 = 20 }));
    assert (not (0 = Compare_r1.compare
                   { r1_l1 = 20; r1_l2 = 10 }
                   { r1_l1 = 20; r1_l2 = 20 }));
  end

let intseq = 
  begin
    assert (0 = Compare_intseq.compare INil INil); 
    assert (0 = Compare_intseq.compare
              (ICons (1,INil))
              (ICons (1,INil)));
    assert (not (0 = Compare_intseq.compare
                   (ICons (1,INil))
                   INil));
    assert (not (0 = Compare_intseq.compare
                   INil
                   (ICons (1,INil))));
    assert (not (0 = Compare_intseq.compare
                   INil
                 (let rec i = ICons(1,i) in i)));
  end

let uses_seqs = 
  begin
    let eq x y = 0 = Compare_uses_seqs.compare x y in
      assert (eq (INil,Cons(1.0,Nil)) (INil,Cons(1.0,Nil)));
      assert (not (eq (INil,Cons(1.0,Nil)) (INil,Cons(2.0,Nil))));
      assert (not (eq (ICons (1,INil),Nil) (INil,Nil)));
  end

let poly0 =
  begin
    let eq x y = 0 = Compare_poly0.compare x y in
      assert (eq `T0 `T0);
      assert (not (eq `T1 `T3));
  end

let poly1 = 
  begin
    let eq x y = 0 = Compare_poly1.compare x y in
      assert (eq `T0 `T0);
      assert (eq (`T1 10) (`T1 10));
      assert (not (eq (`T1 20) (`T1 10)));
      assert (not (eq (`T1 20) `T0));
  end

let poly2 = 
  begin
    let eq x y = 0 = Compare_poly2.compare x y in
      assert (eq (P (3, `T0, 0.0)) (P (3, `T0, 0.0)));
      assert (eq (P (4, `T1 10, 2.0)) (P (4, `T1 10, 2.0)));
      assert (not (eq (P (5, `T1 10, 2.0)) (P (5, `T0, 2.0))));
      assert (not (eq (P (6, `T0, 2.0)) (P (6, `T0, 10.0))));
      assert (not (eq (P (0, `T0, 2.0)) (P (7, `T0, 2.0))));
  end


let poly3 =
  begin
    let eq x y = 0 = Compare_poly3.compare x y in
      assert (eq `Nil `Nil);
      assert (eq (`Cons (3,`Nil)) (`Cons (3,`Nil)));
      assert (eq (`Cons (3,`Cons (4,`Nil))) (`Cons (3,`Cons (4,`Nil))));
      assert (not (eq (`Cons (3,`Cons (4,`Nil))) (`Cons (3,`Nil))));
  end

let poly3b = 
  begin
    let eq x y = 0 = Compare_poly3b.compare x y in
      assert (eq (0,`Nil,`F)  (0,`Nil,`F));
      assert (not (eq (0,`Cons (1,`Nil),`F)  (0,`Nil,`F)));
      assert (not (eq (1,`Nil,`F)  (0,`Nil,`F)));
  end


let poly7_8 = 
  begin
    let module M7 = Compare_poly7(Compare_int) in
    let module M8 = Compare_poly8(Compare_int) in
      assert (0 = M7.compare (Foo (`F 0)) (Foo (`F 0)));
      assert (not (0 = M7.compare (Foo (`F 0)) (Foo (`F 1))));
      assert (0 = M8.compare
                {x = `G (`H (`I (Foo (`F 0))))}
                {x = `G (`H (`I (Foo (`F 0))))});
      assert (not
                (0 = M8.compare
                   {x = `G (`H (`I (Foo (`F 0))))}
                   {x = `G (`H (`I (Foo (`F 1))))}));
  end

let poly10 = 
  begin
    let eq x y = 0 = Compare_poly10.compare x y in
      assert (eq `F `F);
      assert (eq `Nil `Nil);
      assert (not (eq `Nil `F));
  end

let mutrec = 
  begin
    let rec cyclic_1 = S (0, cyclic_2)
    and     cyclic_2 = S (1, cyclic_1) in
      assert (not (0 = Compare_mutrec_a.compare cyclic_1 cyclic_2));
      assert (not 
                (0 = Compare_mutrec_d.compare 
                   (`T {l1 = cyclic_1; l2 = cyclic_2})
                   (`T {l1 = cyclic_2; l2 = cyclic_1})));
  end

let pmutrec = 
  begin
    let module M_a = Compare_pmutrec_a(Compare_int)(Compare_bool) in
    let module M_b = Compare_pmutrec_b(Compare_int)(Compare_bool) in
    let module M_c = Compare_pmutrec_c(Compare_int)(Compare_bool) in
    let module M_d = Compare_pmutrec_d(Compare_int)(Compare_bool) in
    
    let rec cyclic_1 = SS (0, cyclic_2, true)
    and     cyclic_2 = SS (1, cyclic_1, true) in
      assert (not (0 = M_a.compare cyclic_1 cyclic_2));
      assert (not 
                (0 = M_d.compare 
                   (`T {pl1 = cyclic_1; pl2 = cyclic_2})
                   (`T {pl1 = cyclic_2; pl2 = cyclic_1})));
  end


let ff1 =
  begin
    let module M = Compare_ff1(Compare_bool) in
      assert (0 = M.compare (F (true,false)) (F (true,false)));
      assert (0 = M.compare (G (-1)) (G (-1)));
      assert (not (0 = M.compare (F (false,true)) (F (true,false))));
      assert (not (0 = M.compare (G (-1)) (G 0)));
      assert (not (0 =M.compare (G (-1)) (F (true, true))));
  end

let ff2 = 
  begin
    let module M = Compare_ff2(Compare_bool)(Compare_bool) in
      assert (0 = M.compare
                (F1 (F2 (Cons (true,Nil), 0, None)))
                (F1 (F2 (Cons (true,Nil), 0, None))));

      assert (not (0 = M.compare
                     (F2 (Nil, 0, None))
                     (F2 (Cons (true,Nil), 0, None))));

      assert (not (0 = M.compare
                     (F2 (Cons (true,Nil), 0, Some true))
                     (F2 (Cons (true,Nil), 0, Some false))));

      assert (not (0 = M.compare
                     (F2 (Cons (true,Nil), 0, None))
                     (F2 (Cons (true,Nil), 0, Some false))));
  end

let tup0 =
  begin
    assert (0 = Compare_tup0.compare () ());
  end

let tup2 = 
  begin
    assert (0 = Compare_tup2.compare (10,5.0) (10,5.0));
    assert (not (0 = Compare_tup2.compare (10,5.0) (11,5.0)));
    assert (not (0 = Compare_tup2.compare (10,5.0) (10,4.0)));
  end

let tup3 =
  begin
    assert (0 = Compare_tup3.compare (10,2.5,true) (10,2.5,true));
    assert (not (0 = Compare_tup3.compare (10,2.5,true) (11,2.5,true)));
    assert (not (0 = Compare_tup3.compare (10,2.5,true) (10,2.4,true)));
    assert (not (0 = Compare_tup3.compare (10,2.5,true) (10,2.5,false)));
  end

let tup4 =
  begin
    assert (0 = Compare_tup4.compare (1,2,true,()) (1,2,true,()));
    assert (not (0 = Compare_tup4.compare (1,2,true,()) (0,2,true,())));
    assert (not (0 = Compare_tup4.compare (1,2,true,()) (1,3,true,())));
    assert (not (0 = Compare_tup4.compare (1,2,true,()) (1,2,false,())));
  end

let t =
  begin
    assert (0 = Compare_t.compare 0 0);
    assert (0 = Compare_t.compare (-10) (-10));
    assert (0 = Compare_t.compare 14 14);
    assert (not (0 = Compare_t.compare 14 0));
    assert (not (0 = Compare_t.compare 0 14));
    assert (not (0 = Compare_t.compare (-1) 0));
  end

let ii =
  begin
    assert (0 = Compare_ii.compare
	      {int32 = 0l ; int64 = 1L ; nativeint = 2n; }
	      {int32 = 0l ; int64 = 1L ; nativeint = 2n; });
    assert (not (0 = Compare_ii.compare
	      {int32 = 0l ; int64 = 1L ; nativeint = 2n; }
	      {int32 = 1l ; int64 = 1L ; nativeint = 2n; }));
    assert (not (0 = Compare_ii.compare
	      {int32 = 0l ; int64 = 1L ; nativeint = 2n; }
	      {int32 = 0l ; int64 = 2L ; nativeint = 2n; }));
    assert (not (0 = Compare_ii.compare
	      {int32 = 0l ; int64 = 1L ; nativeint = 2n; }
	      {int32 = 0l ; int64 = 1L ; nativeint = 3n; }));
  end

let ii' =
  begin
    assert (0 = Compare_ii'.compare
	      {int32' = 0l ; int64' = 1L ; }
	      {int32' = 0l ; int64' = 1L ; });
    assert (not (0 = Compare_ii'.compare
	      {int32' = 0l ; int64' = 1L ; }
	      {int32' = 1l ; int64' = 1L ; }));
    assert (not (0 = Compare_ii'.compare
	      {int32' = 0l ; int64' = 1L ; }
	      {int32' = 0l ; int64' = 2L ; }));
  end
