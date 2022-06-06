{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QalgebrasZ45ZpolynomialZ45Zendofunctors where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qhomotopies
import qualified MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple

-- foundation.algebras-polynomial-endofunctors.algebra-polynomial-endofunctor-UU
d_algebra'45'polynomial'45'endofunctor'45'UU_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> ()
d_algebra'45'polynomial'45'endofunctor'45'UU_14 = erased
-- foundation.algebras-polynomial-endofunctors.type-algebra-polynomial-endofunctor
d_type'45'algebra'45'polynomial'45'endofunctor_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'algebra'45'polynomial'45'endofunctor_34 = erased
-- foundation.algebras-polynomial-endofunctors.structure-algebra-polynomial-endofunctor
d_structure'45'algebra'45'polynomial'45'endofunctor_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_structure'45'algebra'45'polynomial'45'endofunctor_50 ~v0 ~v1 ~v2
                                                       ~v3 ~v4 v5
  = du_structure'45'algebra'45'polynomial'45'endofunctor_50 v5
du_structure'45'algebra'45'polynomial'45'endofunctor_50 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_structure'45'algebra'45'polynomial'45'endofunctor_50 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation.algebras-polynomial-endofunctors.hom-algebra-polynomial-endofunctor
d_hom'45'algebra'45'polynomial'45'endofunctor_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_hom'45'algebra'45'polynomial'45'endofunctor_70 = erased
-- foundation.algebras-polynomial-endofunctors.map-hom-algebra-polynomial-endofunctor
d_map'45'hom'45'algebra'45'polynomial'45'endofunctor_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'hom'45'algebra'45'polynomial'45'endofunctor_98 ~v0 ~v1 ~v2
                                                        ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_map'45'hom'45'algebra'45'polynomial'45'endofunctor_98 v8
du_map'45'hom'45'algebra'45'polynomial'45'endofunctor_98 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'hom'45'algebra'45'polynomial'45'endofunctor_98 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v0)
-- foundation.algebras-polynomial-endofunctors.structure-hom-algebra-polynomial-endofunctor
d_structure'45'hom'45'algebra'45'polynomial'45'endofunctor_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_structure'45'hom'45'algebra'45'polynomial'45'endofunctor_124
  = erased
-- foundation.algebras-polynomial-endofunctors.htpy-hom-algebra-polynomial-endofunctor
d_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_152 = erased
-- foundation.algebras-polynomial-endofunctors.refl-htpy-hom-algebra-polynomial-endofunctor
d_refl'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_186 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_refl'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_186
du_refl'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_186 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_186
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased erased
-- foundation.algebras-polynomial-endofunctors.htpy-hom-algebra-polynomial-endofunctor-eq
d_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_222 ~v0
                                                                ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                                                                ~v10
  = du_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_222
du_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_222 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_222
  = coe
      du_refl'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_186
-- foundation.algebras-polynomial-endofunctors.is-contr-total-htpy-hom-algebra-polynomial-endofunctor
d_is'45'contr'45'total'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_248 ~v0
                                                                                  ~v1 ~v2 v3 ~v4 ~v5
                                                                                  ~v6 ~v7 v8
  = du_is'45'contr'45'total'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_248
      v3 v8
du_is'45'contr'45'total'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_248 v0
                                                                                   v1
  = coe
      MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'structure_34
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            du_map'45'hom'45'algebra'45'polynomial'45'endofunctor_98 (coe v1))
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
            (coe
               (\ v2 ->
                  coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                    (coe
                       MAlonzo.Code.Qfoundation.Qhomotopies.du_equiv'45'concat'45'htpy_536
                       erased (coe v2))
                    (coe
                       MAlonzo.Code.Qfoundation.Qhomotopies.du_equiv'45'concat'45'htpy_536
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                          (coe v1))
                       (coe v2)))))
         (coe
            MAlonzo.Code.Qfoundation.Qhomotopies.du_is'45'contr'45'total'45'htpy_210
            (coe ()) (coe v0)
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
               (coe v1))))
-- foundation.algebras-polynomial-endofunctors.is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq
d_is'45'equiv'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_292 ~v0
                                                                               ~v1 ~v2 ~v3 ~v4 ~v5
                                                                               ~v6 ~v7 v8
  = du_is'45'equiv'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_292
      v8
du_is'45'equiv'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_292 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor'45'eq_292 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.algebras-polynomial-endofunctors.eq-htpy-hom-algebra-polynomial-endofunctor
d_eq'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'htpy'45'hom'45'algebra'45'polynomial'45'endofunctor_320
  = erased
