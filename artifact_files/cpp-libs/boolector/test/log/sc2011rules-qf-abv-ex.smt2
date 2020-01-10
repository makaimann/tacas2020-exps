(set-logic QF_ABV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 16))
(declare-fun z () (_ BitVec 20))
(declare-fun A () (Array (_ BitVec 16) (_ BitVec 32)))
(assert
(let ((c1 (= ((_ sign_extend 12) z) (select A y)))
(A2 (store A ((_ extract 15 0) x) x)))
(let ((c2 (= A A2)))
(let ((c3
(bvslt (concat z (_ bv5 12))
(bvand (bvor (bvxor (bvnot x)
(select A2 ((_ zero_extend 12) #b1111)))
(concat #xAF02 y))
(concat ((_ extract 15 0)
(bvmul x (select (store A y x) #x35FB)))
(bvashr (_ bv42 16) #x0001))))))
(and c1 (xor c2 c3))))))
(check-sat)
(exit)
