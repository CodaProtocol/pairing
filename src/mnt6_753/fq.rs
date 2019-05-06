use super::fq3::Fq3;
use ff::{Field, PrimeField, PrimeFieldDecodingError, PrimeFieldRepr};

// A coefficient of MNT6-753 G1, 11.
pub const A_COEFF: Fq = Fq(FqRepr([
    0xB, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
]));

// B coefficient of MNT6-753 G1, 11625908999541321152027340224010374716841167701783584648338908235410859267060079819722747939267925389062611062156601938166010098747920378738927832658133625454260115409075816187555055859490253375704728027944315501122723426879114.
pub const B_COEFF: Fq = Fq(FqRepr([
    0x85540b13dfc8468a,
    0x5aba7505ba6fcf24,
    0x867c4e80f4747fde,
    0x3585f9a80a95f401,
    0xbf847957c34cca1e,
    0x7a1a1e0fcf2c43d7,
    0xf62f03b22a9a3c73,
    0xe0a25714b7985993,
    0xbb01b10e60a5d5df,
    0x1468d14ae9bb64b2,
    0xc79d56446237ce2e,
    0x7da285e70863,
]));

// Generator of G1
// X = 16364236387491689444759057944334173579070747473738339749093487337644739228935268157504218078126401066954815152892688541654726829424326599038522503517302466226143788988217410842672857564665527806044250003808514184274233938437290,
// Y = 4510127914410645922431074687553594593336087066778984214797709122300210966076979927285161950203037801392624582544098750667549188549761032654706830225743998064330900301346566408501390638273322467173741629353517809979540986561128,
// Z = 1.
pub const G1_GENERATOR_X: Fq = Fq(FqRepr([
    0xcc3f361fb1f064aa,
    0x567e0e74c1b7ff94,
    0xe4a05ddfae9b2e1a,
    0x91a64b685106d5f1,
    0xcbc9eebe1ce9b83f,
    0x0ac64c9fcb46da65,
    0xaa770dad44f59f26,
    0xf4962eca2a213ffe,
    0xfa411854cf0a44c0,
    0x3a19987126cb808d,
    0x261dbe17959758b3,
    0xb0d6e141836d,
]));

pub const G1_GENERATOR_Y: Fq = Fq(FqRepr([
    0xfdf00e16446a8268,
    0x234bcc4ad6d9f1b3,
    0xedff5513bf5c9a4d,
    0x031577a744c336e1,
    0xc9eb56e9bcc9233e,
    0x74feb51ba730f83f,
    0x91576d1b4a150767,
    0x0fe5d3f4f63e46ac,
    0x6f59b4cc8dda8bff,
    0x66ffec9438150ad0,
    0x5bd0130430294389,
    0x30bd0dcb53b8,
]));

// A coefficient of MNT6-753 G2 =
// mnt6753_twist_coeff_a = mnt6753_Fq3(mnt6753_Fq::zero(), mnt6753_Fq::zero(),
//                                  mnt6753_G1::coeff_a);
//  = (ZERO, ZERO, A_COEFF);
pub const G2_A_COEFF: Fq3 = Fq3 {
    c0: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    c1: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    c2: Fq(FqRepr([
        0xB, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
};

// B coefficient of MNT6-753 G2 =
// mnt6753_twist_coeff_b = mnt6753_Fq3(mnt6753_G1::coeff_b * mnt6753_Fq3::non_residue,
//                                  mnt6753_Fq::zero(), mnt6753_Fq::zero());
// non_residue = mnt6753_Fq3::non_residue = mnt6753_Fq("11");
//  = (G1_B_COEFF * NON_RESIDUE, ZERO, ZERO);
//  =
//  (230882019742962296493853858244225403170161666727738066182014558755430341997815834074953540301336954589899939461041495346549041380428005019617011119979581448158398689102325107764091521640267500616113367696854,
//  0, 0)
pub const G2_B_COEFF: Fq3 = Fq3 {
    c0: Fq(FqRepr([
        0x54a0b982c6a45d6,
        0xb58cf1ccc4e5cef2,
        0xfba5b1b768b764d5,
        0x3ef89b0f60b37e38,
        0xff4400bdc155a172,
        0xaaca7252c3260b5a,
        0x73a18839b19e9de6,
        0x1d0aa6b95996c585,
        0x8af1ec57fbff0e01,
        0xbeb3137141096a78,
        0x2e06614a4630,
        0x0,
    ])),
    c1: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    c2: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
};

// Generator of G2
// These are three Fq elements each because X and Y (and Z) are elements of Fq^3
// X = 46538297238006280434045879335349383221210789488441126073640895239023832290080310125413049878152095926176013036314720850781686614265244307536450228450615346834324267478485994670716807428718518299710702671895190475661871557310,
// 10329739935427016564561842963551883445915701424214177782911128765230271790215029185795830999583638744119368571742929964793955375930677178544873424392910884024986348059137449389533744851691082159233065444766899262771358355816328,
// 19962817058174334691864015232062671736353756221485896034072814261894530786568591431279230352444205682361463997175937973249929732063490256813101714586199642571344378012210374327764059557816647980334733538226843692316285591005879,
// Y = 5648166377754359996653513138027891970842739892107427747585228022871109585680076240624013411622970109911154113378703562803827053335040877618934773712021441101121297691389632155906182656254145368668854360318258860716497525179898,
// 26817850356025045630477313828875808893994935265863280918207940412617168254772789578700316551065949899971937475487458539503514034928974530432009759562975983077355912050606509147904958229398389093697494174311832813615564256810453,
// 32332319709358578441696731586704495581796858962594701633932927358040566210788542624963749336109940335257143899293177116050031684054348958813290781394131284657165540476824211295508498842102093219808642563477603392470909217611033,
// Z = 1.
pub const G2_GENERATOR_X_C0: Fq = Fq(FqRepr([
    0x307398935e322abe,
    0xa5e2e2bb49ed9bc4,
    0xdeea136283b151d5,
    0xd7c97fc6f31c5400,
    0xc4b0c07db85bb497,
    0xe24fd7609d3ee34f,
    0xa80ef19e3ea7cc6f,
    0xfa612a8b527ad4e2,
    0xe54a99973f63ce16,
    0xe3c837ce1eee658d,
    0xb1b6445678bf3030,
    0x80bef89a96,
]));

pub const G2_GENERATOR_X_C1: Fq = Fq(FqRepr([
    0xdf2d87c1daddff88,
    0xc779b9c5c2667ef3,
    0xfc20f5b0842409aa,
    0xf0cf796a3ff0fc15,
    0x8c2fe2e7e5170ed3,
    0x957b5bfa0caa5c83,
    0x276389dcd2f35ce4,
    0x79e3466dfef8efdc,
    0x0f86d7de313b1d64,
    0x8dc54dc512e74779,
    0x50067134915e0bd2,
    0x6fa0bbae3993,
]));

pub const G2_GENERATOR_X_C2: Fq = Fq(FqRepr([
    0x9a001565446aaab7,
    0x11735f03e80fa4e8,
    0x19a5f4a2956d5334,
    0xefbde1a6dc844b83,
    0xa9557b80795e6153,
    0x64f649dedae443e8,
    0x35d7e2ba2dba8800,
    0x5c6ecb626c531a71,
    0xc513ae7ee0ebd05f,
    0x62d1c465176a9c94,
    0x60f5cef6ff5e06ec,
    0xd7ba2e89ecf7,
]));

pub const G2_GENERATOR_Y_C0: Fq = Fq(FqRepr([
    0x51346ff8b4d685fa,
    0xe934e37715a113c5,
    0xc794fc5051654b17,
    0xa21f538fb4f38ca7,
    0x89dd1a726f9a9692,
    0x1521a1543dee6ca9,
    0x7baf99f2409cdad9,
    0x3fbec42ded8ea887,
    0x36911885f0ad158e,
    0xec6e53ec5307e09d,
    0x58f602437a504deb,
    0x3d09620f2aa9,
]));

pub const G2_GENERATOR_Y_C1: Fq = Fq(FqRepr([
    0x410fe5125aa195d5,
    0xe1da54dc42a93c64,
    0x19d65485dc0b9aa6,
    0xbf27d5191c190bd0,
    0xb94011c58d9ff323,
    0x630b1f823f81d632,
    0xc913b3f18b45881d,
    0x553b46cde5be3f51,
    0x61b0d0919d3ca64d,
    0xf8004d7168a7d205,
    0x659e1b67d7e0281c,
    0x121ce4dfcf092,
]));

pub const G2_GENERATOR_Y_C2: Fq = Fq(FqRepr([
    0xc49ff52064431d19,
    0x2ed6f0f661565a99,
    0x2ae0f86dcd355d22,
    0xe95b8f7a514e6753,
    0x2e4d1b4b1620312e,
    0xf206aaa02274f43f,
    0x839ed201f2c59514,
    0x1b3e7e384a6efd52,
    0xe1eeb3c5d08388e2,
    0x5d34bf9d030bd08f,
    0x4a70701127a8296a,
    0x15d65d23cc5cd,
]));

// Coefficients for the Frobenius automorphism.
pub const FROBENIUS_COEFF_FQ3_C1: [Fq; 3] = [
    Fq(FqRepr([
        0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    Fq(FqRepr([
        0x781b72fbc99a1964,
        0xac4965ba6d347570,
        0x269e9ebd7f381482,
        0xc25f088bdeaa96e6,
        0xfb5ec688b3bdef7a,
        0xe8269e0cc7305197,
        0x9681c44e39552f77,
        0xee4c4c1ed83019ea,
        0xc36b0487a10b6591,
        0x153e614fa02bc7cc,
        0xccf7630018181216,
        0x104bfca50c155,
    ])),
    Fq(FqRepr([
        0x60ec03e67665e69c,
        0xa257335ca26cc4df,
        0xb024e2febfc84314,
        0xf780f0ea55eea3be,
        0x438d040b756336bb,
        0xca45be1c01295803,
        0x034f608b6805c825,
        0x19b16d071070d3a3,
        0x9b4ce471cb8c72e1,
        0xa2bb3600bb63e820,
        0x432b2d22d6cabb97,
        0xc006634202bb,
    ])),
];

/*
// Note C2 is just C1 with the second and third element in reverse order
pub const FROBENIUS_COEFF_FQ3_C2: [Fq; 3] = [
    Fq(FqRepr([
        0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    Fq(FqRepr([
        0x60ec03e67665e69c,
        0xa257335ca26cc4df,
        0xb024e2febfc84314,
        0xf780f0ea55eea3be,
        0x438d040b756336bb,
        0xca45be1c01295803,
        0x034f608b6805c825,
        0x19b16d071070d3a3,
        0x9b4ce471cb8c72e1,
        0xa2bb3600bb63e820,
        0x432b2d22d6cabb97,
        0xc006634202bb,
    ])),
    Fq(FqRepr([
        0x781b72fbc99a1964,
        0xac4965ba6d347570,
        0x269e9ebd7f381482,
        0xc25f088bdeaa96e6,
        0xfb5ec688b3bdef7a,
        0xe8269e0cc7305197,
        0x9681c44e39552f77,
        0xee4c4c1ed83019ea,
        0xc36b0487a10b6591,
        0x153e614fa02bc7cc,
        0xccf7630018181216,
        0x104bfca50c155,
    ])),
];
*/
pub const FROBENIUS_COEFF_FQ6_C1: [Fq; 6] = [
    Fq(FqRepr([
        0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    Fq(FqRepr([
        0x781b72fbc99a1965,
        0xac4965ba6d347570,
        0x269e9ebd7f381482,
        0xc25f088bdeaa96e6,
        0xfb5ec688b3bdef7a,
        0xe8269e0cc7305197,
        0x9681c44e39552f77,
        0xee4c4c1ed83019ea,
        0xc36b0487a10b6591,
        0x153e614fa02bc7cc,
        0xccf7630018181216,
        0x104bfca50c155,
    ])),
    Fq(FqRepr([
        0x781b72fbc99a1964,
        0xac4965ba6d347570,
        0x269e9ebd7f381482,
        0xc25f088bdeaa96e6,
        0xfb5ec688b3bdef7a,
        0xe8269e0cc7305197,
        0x9681c44e39552f77,
        0xee4c4c1ed83019ea,
        0xc36b0487a10b6591,
        0x153e614fa02bc7cc,
        0xccf7630018181216,
        0x104bfca50c155,
    ])),
    Fq(FqRepr([
        0xd90776e240000000,
        0x4ea099170fa13a4f,
        0xd6c381bc3f005797,
        0xb9dff97634993aa4,
        0x3eebca9429212636,
        0xb26c5c28c859a99b,
        0x99d124d9a15af79d,
        0x07fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ])),
    Fq(FqRepr([
        0x60ec03e67665e69c,
        0xa257335ca26cc4df,
        0xb024e2febfc84314,
        0xf780f0ea55eea3be,
        0x438d040b756336bb,
        0xca45be1c01295803,
        0x034f608b6805c825,
        0x19b16d071070d3a3,
        0x9b4ce471cb8c72e1,
        0xa2bb3600bb63e820,
        0x432b2d22d6cabb97,
        0xc006634202bb,
    ])),
    Fq(FqRepr([
        0x60ec03e67665e69d,
        0xa257335ca26cc4df,
        0xb024e2febfc84314,
        0xf780f0ea55eea3be,
        0x438d040b756336bb,
        0xca45be1c01295803,
        0x034f608b6805c825,
        0x19b16d071070d3a3,
        0x9b4ce471cb8c72e1,
        0xa2bb3600bb63e820,
        0x432b2d22d6cabb97,
        0xc006634202bb,
    ])),
];

// This is negative one wrt the limbs, mod q
// -((2**756) mod q) mod q
pub const NEGATIVE_ONE: Fq = Fq(FqRepr([
    0x1f70f6cdc00090bf,
    0xffef30ff5a176ba7,
    0x34d7aee33286761d,
    0xaa6d9cc76f4f79ca,
    0x93df7bad553a4b62,
    0x12afb31fea4cde38,
    0x67c4e9228e277305,
    0xae72762315b0e32b,
    0x1e431f2d6f0b3251,
    0xa85518752329c761,
    0x7add306fcee92c18,
    0x1497e8ec9e1ce,
]));

#[derive(PrimeField)]
#[PrimeFieldModulus = "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888458477323173057491593855069696241854796396165721416325350064441470418137846398469611935719059908164220784476160001"]
#[PrimeFieldGenerator = "17"]
pub struct Fq(FqRepr);

impl Fq {
    pub fn mul_by_nonresidue(&mut self) {
        self.mul_assign(&Fq(FqRepr::from(11)))
    }
}

#[test]
fn test_a_coeff() {
    assert_eq!(Fq::from_repr(FqRepr::from(5)).unwrap(), A_COEFF);
}

#[test]
fn test_neg_one() {
    let mut o = Fq::one();
    o.negate();

    assert_eq!(NEGATIVE_ONE, o);
}

#[cfg(test)]
use rand::{Rand, SeedableRng, XorShiftRng};

#[test]
fn test_fq_repr_ordering() {
    use std::cmp::Ordering;

    fn assert_equality(a: FqRepr, b: FqRepr) {
        assert_eq!(a, b);
        assert!(a.cmp(&b) == Ordering::Equal);
    }

    fn assert_lt(a: FqRepr, b: FqRepr) {
        assert!(a < b);
        assert!(b > a);
    }

    assert_equality(
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999,
        ]),
    );
    assert_equality(
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9998, 9999, 9999, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9998, 9999, 9999, 9999, 9999,
        ]),
    );
    assert_equality(
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
    assert_lt(
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9998, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
    assert_lt(
        FqRepr([
            9999, 9999, 9999, 9997, 9998, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
    assert_lt(
        FqRepr([
            9, 9999, 9999, 9997, 9998, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
}

#[test]
fn test_fq_repr_from() {
    assert_eq!(
        FqRepr::from(100),
        FqRepr([100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    );
}

#[test]
fn test_fq_repr_is_odd() {
    assert!(!FqRepr::from(0).is_odd());
    assert!(FqRepr::from(0).is_even());
    assert!(FqRepr::from(1).is_odd());
    assert!(!FqRepr::from(1).is_even());
    assert!(!FqRepr::from(324834872).is_odd());
    assert!(FqRepr::from(324834872).is_even());
    assert!(FqRepr::from(324834873).is_odd());
    assert!(!FqRepr::from(324834873).is_even());
}

#[test]
fn test_fq_repr_is_zero() {
    assert!(FqRepr::from(0).is_zero());
    assert!(!FqRepr::from(1).is_zero());
    assert!(!FqRepr([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]).is_zero());
}

#[test]
fn test_fq_repr_num_bits() {
    let mut a = FqRepr::from(0);
    assert_eq!(0, a.num_bits());
    a = FqRepr::from(1);
    for i in 1..385 {
        assert_eq!(i, a.num_bits());
        a.mul2();
    }
    assert_eq!(0, a.num_bits());
}

#[test]
fn test_fq_repr_sub_noborrow() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let mut a = FqRepr::rand(&mut rng);
        a.0[5] >>= 30;
        let mut b = a;
        for _ in 0..10 {
            b.mul2();
        }
        let mut c = b;
        for _ in 0..10 {
            c.mul2();
        }

        assert!(a < b);
        assert!(b < c);

        let mut csub_ba = c;
        csub_ba.sub_noborrow(&b);
        csub_ba.sub_noborrow(&a);

        let mut csub_ab = c;
        csub_ab.sub_noborrow(&a);
        csub_ab.sub_noborrow(&b);

        assert_eq!(csub_ab, csub_ba);
    }

    // Subtracting q+1 from q should produce -1
    let mut qplusone = FqRepr([
        0xd90776e240000001,
        0x4ea099170fa13a4f,
        0xd6c381bc3f005797,
        0xb9dff97634993aa4,
        0x3eebca9429212636,
        0xb26c5c28c859a99b,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]);
    qplusone.sub_noborrow(&FqRepr([
        0xd90776e240000002,
        0x4ea099170fa13a4f,
        0xd6c381bc3f005797,
        0xb9dff97634993aa4,
        0x3eebca9429212636,
        0xb26c5c28c859a99b,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]));
    assert_eq!(
        qplusone,
        FqRepr([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
        ])
    );
}

#[test]
fn test_fq_repr_add_nocarry() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    // Test for the associativity of addition.
    for _ in 0..1000 {
        let mut a = FqRepr::rand(&mut rng);
        let mut b = FqRepr::rand(&mut rng);
        let mut c = FqRepr::rand(&mut rng);

        // Unset the first few bits, so that overflow won't occur.
        a.0[5] >>= 3;
        b.0[5] >>= 3;
        c.0[5] >>= 3;

        let mut abc = a;
        abc.add_nocarry(&b);
        abc.add_nocarry(&c);

        let mut acb = a;
        acb.add_nocarry(&c);
        acb.add_nocarry(&b);

        let mut bac = b;
        bac.add_nocarry(&a);
        bac.add_nocarry(&c);

        let mut bca = b;
        bca.add_nocarry(&c);
        bca.add_nocarry(&a);

        let mut cab = c;
        cab.add_nocarry(&a);
        cab.add_nocarry(&b);

        let mut cba = c;
        cba.add_nocarry(&b);
        cba.add_nocarry(&a);

        assert_eq!(abc, acb);
        assert_eq!(abc, bac);
        assert_eq!(abc, bca);
        assert_eq!(abc, cab);
        assert_eq!(abc, cba);
    }

    // Adding 1 to (q - 1) should produce zero
    let mut x = FqRepr([
        0x1f70f6cdc00090bf,
        0xffef30ff5a176ba7,
        0x34d7aee33286761d,
        0xaa6d9cc76f4f79ca,
        0x93df7bad553a4b62,
        0x12afb31fea4cde38,
        0x67c4e9228e277305,
        0xae72762315b0e32b,
        0x1e431f2d6f0b3251,
        0xa85518752329c761,
        0x7add306fcee92c18,
        0x1497e8ec9e1ce,
    ]);
    x.add_nocarry(&FqRepr::from(1));
    assert!(x.is_zero());
}

#[test]
fn test_fq_is_valid() {
    let mut a = Fq(MODULUS);
    assert!(!a.is_valid());
    a.0.sub_noborrow(&FqRepr::from(1));
    assert!(a.is_valid());
    assert!(Fq(FqRepr::from(0)).is_valid());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let a = Fq::rand(&mut rng);
        assert!(a.is_valid());
    }
}

#[test]
fn test_fq_add_assign() {
    /*
        {
            // Random number
            let mut tmp = Fq(FqRepr([
            ]));
            assert!(tmp.is_valid());
            // Test that adding zero has no effect.
            tmp.add_assign(&Fq(FqRepr::from(0)));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );
            // Add one and test for the result.
            tmp.add_assign(&Fq(FqRepr::from(1)));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );
            // Add another random number that exercises the reduction.
            tmp.add_assign(&Fq(FqRepr([
            ])));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );
            // Add one to (q - 1) and test for the result.
            tmp = Fq(FqRepr([
            ]));
            tmp.add_assign(&Fq(FqRepr::from(1)));
            assert!(tmp.0.is_zero());
            // Add a random number to another one such that the result is q - 1
            tmp = Fq(FqRepr([
            ]));
            tmp.add_assign(&Fq(FqRepr([
            ])));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );
            // Add one to the result and test for it.
            tmp.add_assign(&Fq(FqRepr::from(1)));
            assert!(tmp.0.is_zero());
        }
    */
    // Test associativity

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Generate a, b, c and ensure (a + b) + c == a + (b + c).
        let a = Fq::rand(&mut rng);
        let b = Fq::rand(&mut rng);
        let c = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.add_assign(&b);
        tmp1.add_assign(&c);

        let mut tmp2 = b;
        tmp2.add_assign(&c);
        tmp2.add_assign(&a);

        assert!(tmp1.is_valid());
        assert!(tmp2.is_valid());
        assert_eq!(tmp1, tmp2);
    }
}

#[test]
fn test_fq_sub_assign() {
    /*
        {
            // Test arbitrary subtraction that tests reduction.
            let mut tmp = Fq(FqRepr([
            ]));
            tmp.sub_assign(&Fq(FqRepr([
            ])));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );

            // Test the opposite subtraction which doesn't test reduction.
            tmp = Fq(FqRepr([
            ]));
            tmp.sub_assign(&Fq(FqRepr([
            ])));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );

            // Test for sensible results with zero
            tmp = Fq(FqRepr::from(0));
            tmp.sub_assign(&Fq(FqRepr::from(0)));
            assert!(tmp.is_zero());

            tmp = Fq(FqRepr([
            ]));
            tmp.sub_assign(&Fq(FqRepr::from(0)));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );
        }
    */
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Ensure that (a - b) + (b - a) = 0.
        let a = Fq::rand(&mut rng);
        let b = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.sub_assign(&b);

        let mut tmp2 = b;
        tmp2.sub_assign(&a);

        tmp1.add_assign(&tmp2);
        assert!(tmp1.is_zero());
    }
}

#[test]
fn test_fq_mul_assign() {
    let mut tmp = Fq(FqRepr([
        0xbf5fe920d1992880,
        0xe9433a42ccefbff2,
        0xd7f812c1def8c709,
        0xc9186f2f58446f50,
        0xb917d238a7c19af1,
        0xb8d279edb5f43215,
        0x1a004589295e39c7,
        0x53034ee27b5a6dfa,
        0x39e094c7e6e2ac7f,
        0xe52b2e27c5435e57,
        0x5a58f3a8f955e7f,
        0x1463240606093,
    ]));
    tmp.mul_assign(&Fq(FqRepr([
        0x3f5caa8a351082e0,
        0x10e2cbfdb8a93405,
        0xfff3511518ddee13,
        0x81c6b5eae9770cc6,
        0xc5ef81f4273603ef,
        0x11c668d5e825ed48,
        0xc6f28e3f772ce1c5,
        0xbf4aa406ab3a9757,
        0x6984799c3cae5b97,
        0xde4a63b3a95e8ee5,
        0xbf4d903aa33977e1,
        0xd07c25be7743,
    ])));
    assert!(
        tmp == Fq(FqRepr([
            0x4b2cd72171331b9d,
            0x8dde609d06a26f9d,
            0x13204e1c288c8bbe,
            0x368291a479d84648,
            0x1962bb9dabd0c52f,
            0x43af438a16ac1592,
            0x3688aad7d4b9919c,
            0xf031665a127582d7,
            0x42b3219495400fa8,
            0xbb04927b51dd808c,
            0x669d5702378dabcf,
            0x280f8a033a8f,
        ]))
    );

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000000 {
        // Ensure that (a * b) * c = a * (b * c)
        let a = Fq::rand(&mut rng);
        let b = Fq::rand(&mut rng);
        let c = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.mul_assign(&b);
        tmp1.mul_assign(&c);

        let mut tmp2 = b;
        tmp2.mul_assign(&c);
        tmp2.mul_assign(&a);

        assert_eq!(tmp1, tmp2);
    }

    for _ in 0..1000000 {
        // Ensure that r * (a + b + c) = r*a + r*b + r*c

        let r = Fq::rand(&mut rng);
        let mut a = Fq::rand(&mut rng);
        let mut b = Fq::rand(&mut rng);
        let mut c = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.add_assign(&b);
        tmp1.add_assign(&c);
        tmp1.mul_assign(&r);

        a.mul_assign(&r);
        b.mul_assign(&r);
        c.mul_assign(&r);

        a.add_assign(&b);
        a.add_assign(&c);

        assert_eq!(tmp1, a);
    }
}

#[test]
fn test_fq_squaring() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000000 {
        // Ensure that (a * a) = a^2
        let a = Fq::rand(&mut rng);

        let mut tmp = a;
        tmp.square();

        let mut tmp2 = a;
        tmp2.mul_assign(&a);

        assert_eq!(tmp, tmp2);
    }
}

#[test]
fn test_fq_inverse() {
    assert!(Fq::zero().inverse().is_none());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let one = Fq::one();

    for _ in 0..1000 {
        // Ensure that a * a^-1 = 1
        let mut a = Fq::rand(&mut rng);
        let ainv = a.inverse().unwrap();
        a.mul_assign(&ainv);
        assert_eq!(a, one);
    }
}

#[test]
fn test_fq_double() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Ensure doubling a is equivalent to adding a to itself.
        let mut a = Fq::rand(&mut rng);
        let mut b = a;
        b.add_assign(&a);
        a.double();
        assert_eq!(a, b);
    }
}

#[test]
fn test_fq_negate() {
    {
        let mut a = Fq::zero();
        a.negate();

        assert!(a.is_zero());
    }

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Ensure (a - (-a)) = 0.
        let mut a = Fq::rand(&mut rng);
        let mut b = a;
        b.negate();
        a.add_assign(&b);

        assert!(a.is_zero());
    }
}

#[test]
fn test_fq_pow() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for i in 0..1000 {
        // Exponentiate by various small numbers and ensure it consists with repeated
        // multiplication.
        let a = Fq::rand(&mut rng);
        let target = a.pow(&[i]);
        let mut c = Fq::one();
        for _ in 0..i {
            c.mul_assign(&a);
        }
        assert_eq!(c, target);
    }

    for _ in 0..1000 {
        // Exponentiating by the modulus should have no effect in a prime field.
        let a = Fq::rand(&mut rng);

        assert_eq!(a, a.pow(Fq::char()));
    }
}

#[test]
fn test_fq_sqrt() {
    use ff::SqrtField;

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    assert_eq!(Fq::zero().sqrt().unwrap(), Fq::zero());

    for _ in 0..1000 {
        // Ensure sqrt(a^2) = a or -a
        let a = Fq::rand(&mut rng);
        let mut nega = a;
        nega.negate();
        let mut b = a;
        b.square();

        let b = b.sqrt().unwrap();

        assert!(a == b || nega == b);
    }

    for _ in 0..1000 {
        // Ensure sqrt(a)^2 = a for random a
        let a = Fq::rand(&mut rng);

        if let Some(mut tmp) = a.sqrt() {
            tmp.square();

            assert_eq!(a, tmp);
        }
    }
}

#[test]
fn test_fq_from_into_repr() {
    // q + 1 should not be in the field
    assert!(Fq::from_repr(FqRepr([
        0xd90776e240000002,
        0x4ea099170fa13a4f,
        0xd6c381bc3f005797,
        0xb9dff97634993aa4,
        0x3eebca9429212636,
        0xb26c5c28c859a99b,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]))
    .is_err());

    // q should not be in the field
    assert!(Fq::from_repr(Fq::char()).is_err());

    // Multiply some arbitrary representations to see if the result is as expected.
    let a = FqRepr([
        0xbf5fe920d1992880,
        0xe9433a42ccefbff2,
        0xd7f812c1def8c709,
        0xc9186f2f58446f50,
        0xb917d238a7c19af1,
        0xb8d279edb5f43215,
        0x1a004589295e39c7,
        0x53034ee27b5a6dfa,
        0x39e094c7e6e2ac7f,
        0xe52b2e27c5435e57,
        0x5a58f3a8f955e7f,
        0x1463240606093,
    ]);
    let mut a_fq = Fq::from_repr(a).unwrap();
    let b = FqRepr([
        0x3f5caa8a351082e0,
        0x10e2cbfdb8a93405,
        0xfff3511518ddee13,
        0x81c6b5eae9770cc6,
        0xc5ef81f4273603ef,
        0x11c668d5e825ed48,
        0xc6f28e3f772ce1c5,
        0xbf4aa406ab3a9757,
        0x6984799c3cae5b97,
        0xde4a63b3a95e8ee5,
        0xbf4d903aa33977e1,
        0xd07c25be7743,
    ]);
    let b_fq = Fq::from_repr(b).unwrap();
    let c = FqRepr([
        0x4b2cd72171331b9d,
        0x8dde609d06a26f9d,
        0x13204e1c288c8bbe,
        0x368291a479d84648,
        0x1962bb9dabd0c52f,
        0x43af438a16ac1592,
        0x3688aad7d4b9919c,
        0xf031665a127582d7,
        0x42b3219495400fa8,
        0xbb04927b51dd808c,
        0x669d5702378dabcf,
        0x280f8a033a8f,
    ]);
    a_fq.mul_assign(&b_fq);
    assert_eq!(a_fq.into_repr(), c);

    // Zero should be in the field.
    assert!(Fq::from_repr(FqRepr::from(0)).unwrap().is_zero());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Try to turn Fq elements into representations and back again, and compare.
        let a = Fq::rand(&mut rng);
        let a_repr = a.into_repr();
        let b_repr = FqRepr::from(a);
        assert_eq!(a_repr, b_repr);
        let a_again = Fq::from_repr(a_repr).unwrap();

        assert_eq!(a, a_again);
    }
}

#[test]
fn test_fq_num_bits() {
    assert_eq!(Fq::NUM_BITS, 753);
    assert_eq!(Fq::CAPACITY, 752);
}

#[test]
fn fq_field_tests() {
    ::tests::field::random_field_tests::<Fq>();
    ::tests::field::random_sqrt_tests::<Fq>();
    ::tests::field::random_frobenius_tests::<Fq, _>(Fq::char(), 13);
    ::tests::field::from_str_tests::<Fq>();
}

#[test]
fn test_fq_ordering() {
    // FqRepr's ordering is well-tested, but we still need to make sure the Fq
    // elements aren't being compared in Montgomery form.
    for i in 0..100 {
        assert!(
            Fq::from_repr(FqRepr::from(i + 1)).unwrap() > Fq::from_repr(FqRepr::from(i)).unwrap()
        );
    }
}

#[test]
fn fq_repr_tests() {
    ::tests::repr::random_repr_tests::<FqRepr>();
}

#[test]
fn test_fq_legendre() {
    use ff::LegendreSymbol::*;
    use ff::SqrtField;

    assert_eq!(QuadraticResidue, Fq::one().legendre());
    assert_eq!(Zero, Fq::zero().legendre());

    assert_eq!(
        QuadraticNonResidue,
        Fq::from_repr(FqRepr::from(2)).unwrap().legendre()
    );
    assert_eq!(
        QuadraticResidue,
        Fq::from_repr(FqRepr::from(4)).unwrap().legendre()
    );
}
