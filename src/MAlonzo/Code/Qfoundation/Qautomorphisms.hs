{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qautomorphisms where

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

-- foundation.automorphisms.Aut
d_Aut_6 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_Aut_6 = erased
-- foundation.automorphisms.UU-Pointed-Type-With-Aut
d_UU'45'Pointed'45'Type'45'With'45'Aut_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_UU'45'Pointed'45'Type'45'With'45'Aut_12 = erased
-- foundation.automorphisms.type-Pointed-Type-With-Aut
d_type'45'Pointed'45'Type'45'With'45'Aut_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'Pointed'45'Type'45'With'45'Aut_20 = erased
-- foundation.automorphisms.point-Pointed-Type-With-Aut
d_point'45'Pointed'45'Type'45'With'45'Aut_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_point'45'Pointed'45'Type'45'With'45'Aut_28 ~v0 v1
  = du_point'45'Pointed'45'Type'45'With'45'Aut_28 v1
du_point'45'Pointed'45'Type'45'With'45'Aut_28 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_point'45'Pointed'45'Type'45'With'45'Aut_28 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v0))
-- foundation.automorphisms.aut-Pointed-Type-With-Aut
d_aut'45'Pointed'45'Type'45'With'45'Aut_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_aut'45'Pointed'45'Type'45'With'45'Aut_36 ~v0 v1
  = du_aut'45'Pointed'45'Type'45'With'45'Aut_36 v1
du_aut'45'Pointed'45'Type'45'With'45'Aut_36 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_aut'45'Pointed'45'Type'45'With'45'Aut_36 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v0))
-- foundation.automorphisms.map-aut-Pointed-Type-With-Aut
d_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44 ~v0 v1
  = du_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44 v1
du_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'aut'45'Pointed'45'Type'45'With'45'Aut_44 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe du_aut'45'Pointed'45'Type'45'With'45'Aut_36 (coe v0))
-- foundation.automorphisms.inv-map-aut-Pointed-Type-With-Aut
d_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52 ~v0 v1
  = du_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52 v1
du_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_52 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe du_aut'45'Pointed'45'Type'45'With'45'Aut_36 (coe v0))
-- foundation.automorphisms.issec-inv-map-aut-Pointed-Type-With-Aut
d_issec'45'inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_60
  = erased
-- foundation.automorphisms.isretr-inv-map-aut-Pointed-Type-With-Aut
d_isretr'45'inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'inv'45'map'45'aut'45'Pointed'45'Type'45'With'45'Aut_68
  = erased
-- foundation.automorphisms.hom-Pointed-Type-With-Aut
d_hom'45'Pointed'45'Type'45'With'45'Aut_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_hom'45'Pointed'45'Type'45'With'45'Aut_76 = erased
-- foundation.automorphisms.map-hom-Pointed-Type-With-Aut
d_map'45'hom'45'Pointed'45'Type'45'With'45'Aut_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'hom'45'Pointed'45'Type'45'With'45'Aut_96 ~v0 ~v1 ~v2 ~v3
                                                  v4
  = du_map'45'hom'45'Pointed'45'Type'45'With'45'Aut_96 v4
du_map'45'hom'45'Pointed'45'Type'45'With'45'Aut_96 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'hom'45'Pointed'45'Type'45'With'45'Aut_96 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v0)
-- foundation.automorphisms.preserves-point-map-hom-Pointed-Type-With-Aut
d_preserves'45'point'45'map'45'hom'45'Pointed'45'Type'45'With'45'Aut_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'point'45'map'45'hom'45'Pointed'45'Type'45'With'45'Aut_114
  = erased
-- foundation.automorphisms.preserves-aut-map-hom-Pointed-Type-With-Aut
d_preserves'45'aut'45'map'45'hom'45'Pointed'45'Type'45'With'45'Aut_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'aut'45'map'45'hom'45'Pointed'45'Type'45'With'45'Aut_132
  = erased
-- foundation.automorphisms.htpy-hom-Pointed-Type-With-Aut
d_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_152 = erased
-- foundation.automorphisms.refl-htpy-hom-Pointed-Type-With-Aut
d_refl'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_176 ~v0 ~v1
                                                            ~v2 ~v3 ~v4
  = du_refl'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_176
du_refl'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_176 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_176
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased erased)
-- foundation.automorphisms.htpy-hom-Pointed-Type-With-Aut-eq
d_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut'45'eq_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut'45'eq_198 ~v0 ~v1
                                                          ~v2 ~v3 ~v4 ~v5 ~v6
  = du_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut'45'eq_198
du_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut'45'eq_198 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut'45'eq_198
  = coe du_refl'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_176
-- foundation.automorphisms.is-contr-total-htpy-hom-Pointed-Type-With-Aut
d_is'45'contr'45'total'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_216 v0
                                                                            v1 ~v2 ~v3 v4
  = du_is'45'contr'45'total'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_216
      v0 v1 v4
du_is'45'contr'45'total'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_216 v0
                                                                             v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'structure_34
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe du_map'45'hom'45'Pointed'45'Type'45'With'45'Aut_96 (coe v2))
         erased)
      (coe
         MAlonzo.Code.Qfoundation.QstructureZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'structure_34
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            erased erased)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
               (coe
                  MAlonzo.Code.Qfoundation.Qhomotopies.du_equiv'45'concat'45'htpy_536
                  erased))
            (coe
               MAlonzo.Code.Qfoundation.Qhomotopies.du_is'45'contr'45'total'45'htpy_210
               (coe v0) (coe v1) erased)))
-- foundation.automorphisms.is-equiv-htpy-hom-Pointed-Type-With-Aut
d_is'45'equiv'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_262 ~v0
                                                                   ~v1 ~v2 ~v3 v4
  = du_is'45'equiv'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_262
      v4
du_is'45'equiv'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_262 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_262 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.automorphisms.eq-htpy-hom-Pointed-Type-With-Aut
d_eq'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'htpy'45'hom'45'Pointed'45'Type'45'With'45'Aut_282 = erased
