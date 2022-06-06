{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QpolynomialZ45Zendofunctors where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qhomotopies
import qualified MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple

-- foundation.polynomial-endofunctors.type-polynomial-endofunctor
d_type'45'polynomial'45'endofunctor_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> () -> ()
d_type'45'polynomial'45'endofunctor_16 = erased
-- foundation.polynomial-endofunctors._.Eq-type-polynomial-endofunctor
d_Eq'45'type'45'polynomial'45'endofunctor_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_Eq'45'type'45'polynomial'45'endofunctor_46 = erased
-- foundation.polynomial-endofunctors._.refl-Eq-type-polynomial-endofunctor
d_refl'45'Eq'45'type'45'polynomial'45'endofunctor_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'Eq'45'type'45'polynomial'45'endofunctor_56 ~v0 ~v1 ~v2
                                                     ~v3 ~v4 ~v5 v6
  = du_refl'45'Eq'45'type'45'polynomial'45'endofunctor_56 v6
du_refl'45'Eq'45'type'45'polynomial'45'endofunctor_56 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'Eq'45'type'45'polynomial'45'endofunctor_56 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased erased)
-- foundation.polynomial-endofunctors._.is-contr-total-Eq-type-polynomial-endofunctor
d_is'45'contr'45'total'45'Eq'45'type'45'polynomial'45'endofunctor_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'Eq'45'type'45'polynomial'45'endofunctor_64 ~v0
                                                                     v1 v2 ~v3 ~v4 ~v5 v6
  = du_is'45'contr'45'total'45'Eq'45'type'45'polynomial'45'endofunctor_64
      v1 v2 v6
du_is'45'contr'45'total'45'Eq'45'type'45'polynomial'45'endofunctor_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'Eq'45'type'45'polynomial'45'endofunctor_64 v0
                                                                      v1 v2
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
        -> coe
             MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'structure_34
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v3) erased)
             (coe
                MAlonzo.Code.Qfoundation.Qhomotopies.du_is'45'contr'45'total'45'htpy_210
                (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.polynomial-endofunctors._.Eq-type-polynomial-endofunctor-eq
d_Eq'45'type'45'polynomial'45'endofunctor'45'eq_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Eq'45'type'45'polynomial'45'endofunctor'45'eq_80 ~v0 ~v1 ~v2 ~v3
                                                   ~v4 ~v5 v6 ~v7 ~v8
  = du_Eq'45'type'45'polynomial'45'endofunctor'45'eq_80 v6
du_Eq'45'type'45'polynomial'45'endofunctor'45'eq_80 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Eq'45'type'45'polynomial'45'endofunctor'45'eq_80 v0
  = coe
      du_refl'45'Eq'45'type'45'polynomial'45'endofunctor_56 (coe v0)
-- foundation.polynomial-endofunctors._.is-equiv-Eq-type-polynomial-endofunctor-eq
d_is'45'equiv'45'Eq'45'type'45'polynomial'45'endofunctor'45'eq_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'Eq'45'type'45'polynomial'45'endofunctor'45'eq_88 ~v0
                                                                  ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_is'45'equiv'45'Eq'45'type'45'polynomial'45'endofunctor'45'eq_88
      v6
du_is'45'equiv'45'Eq'45'type'45'polynomial'45'endofunctor'45'eq_88 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'Eq'45'type'45'polynomial'45'endofunctor'45'eq_88 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.polynomial-endofunctors._.eq-Eq-type-polynomial-endofunctor
d_eq'45'Eq'45'type'45'polynomial'45'endofunctor_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'Eq'45'type'45'polynomial'45'endofunctor_96 = erased
-- foundation.polynomial-endofunctors._.isretr-eq-Eq-type-polynomial-endofunctor
d_isretr'45'eq'45'Eq'45'type'45'polynomial'45'endofunctor_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'eq'45'Eq'45'type'45'polynomial'45'endofunctor_106
  = erased
-- foundation.polynomial-endofunctors._.coh-refl-eq-Eq-type-polynomial-endofunctor
d_coh'45'refl'45'eq'45'Eq'45'type'45'polynomial'45'endofunctor_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coh'45'refl'45'eq'45'Eq'45'type'45'polynomial'45'endofunctor_114
  = erased
-- foundation.polynomial-endofunctors.map-polynomial-endofunctor
d_map'45'polynomial'45'endofunctor_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'polynomial'45'endofunctor_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_map'45'polynomial'45'endofunctor_136 v8
du_map'45'polynomial'45'endofunctor_136 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'polynomial'45'endofunctor_136 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_tot_24
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
              (coe (\ v2 -> v0))))
-- foundation.polynomial-endofunctors.htpy-polynomial-endofunctor
d_htpy'45'polynomial'45'endofunctor_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_htpy'45'polynomial'45'endofunctor_168 = erased
-- foundation.polynomial-endofunctors.coh-refl-htpy-polynomial-endofunctor
d_coh'45'refl'45'htpy'45'polynomial'45'endofunctor_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_coh'45'refl'45'htpy'45'polynomial'45'endofunctor_206 = erased
