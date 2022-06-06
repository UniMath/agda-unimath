{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qunivalence where

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
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qunivalence
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZdependentZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qequivalences

-- foundation.univalence.univalence
d_univalence_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.univalence.univalence"
-- foundation.univalence.eq-equiv
d_eq'45'equiv_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv_18 = erased
-- foundation.univalence.equiv-univalence
d_equiv'45'univalence_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'univalence_30 v0 ~v1 ~v2 = du_equiv'45'univalence_30 v0
du_equiv'45'univalence_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'univalence_30 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v1 ->
         coe MAlonzo.Code.QfoundationZ45Zcore.Qunivalence.du_equiv'45'eq_10)
      (coe d_univalence_10 v0 erased erased)
-- foundation.univalence.is-contr-total-equiv
d_is'45'contr'45'total'45'equiv_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv_38 ~v0 ~v1
  = du_is'45'contr'45'total'45'equiv_38
du_is'45'contr'45'total'45'equiv_38 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv_38
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qunivalence.du_is'45'contr'45'total'45'equiv'45'UNIVALENCE_32
      erased
-- foundation.univalence.is-contr-total-equiv'
d_is'45'contr'45'total'45'equiv''_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv''_48 ~v0 ~v1
  = du_is'45'contr'45'total'45'equiv''_48
du_is'45'contr'45'total'45'equiv''_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv''_48
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.Qfoundation.Qequivalences.du_equiv'45'inv'45'equiv_858)))
      (coe du_is'45'contr'45'total'45'equiv_38)
-- foundation.univalence.equiv-fam
d_equiv'45'fam_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> ()) -> ()
d_equiv'45'fam_68 = erased
-- foundation.univalence.id-equiv-fam
d_id'45'equiv'45'fam_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'fam_86 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_id'45'equiv'45'fam_86
du_id'45'equiv'45'fam_86 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'fam_86
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92
-- foundation.univalence.equiv-eq-fam
d_equiv'45'eq'45'fam_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'fam_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_equiv'45'eq'45'fam_102
du_equiv'45'eq'45'fam_102 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'fam_102 v0 = coe du_id'45'equiv'45'fam_86
-- foundation.univalence.is-contr-total-equiv-fam
d_is'45'contr'45'total'45'equiv'45'fam_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'fam_114 v0 ~v1 ~v2 ~v3
  = du_is'45'contr'45'total'45'equiv'45'fam_114 v0
du_is'45'contr'45'total'45'equiv'45'fam_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'fam_114 v0
  = coe
      MAlonzo.Code.Qfoundation.QequalityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'contr'45'total'45'Eq'45'Π_28
      (coe v0) (coe (\ v1 -> coe du_is'45'contr'45'total'45'equiv_38))
-- foundation.univalence.is-equiv-equiv-eq-fam
d_is'45'equiv'45'equiv'45'eq'45'fam_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'fam_134 ~v0 ~v1 ~v2 v3
  = du_is'45'equiv'45'equiv'45'eq'45'fam_134 v3
du_is'45'equiv'45'equiv'45'eq'45'fam_134 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'fam_134 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.univalence.eq-equiv-fam
d_eq'45'equiv'45'fam_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'fam_148 = erased
