// MNT4-753 has twist field Fq2
use super::fq2::Fq2;
use ff::{Field, PrimeField, PrimeFieldDecodingError, PrimeFieldRepr};

// A coefficient of MNT4-753 curve, 2.
pub const A_COEFF: Fq = Fq(FqRepr([
    0x2, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
]));

// B coefficient of MNT4-753 curve, 28798803903456388891410036793299405764940372360099938340752576406393880372126970068421383312482853541572780087363938442377933706865252053507077543420534380486492786626556269083255657125025963825610840222568694137138741554679540
pub const B_COEFF: Fq = Fq(FqRepr([
    0x9c9a0491678ef400,
    0xeaad265458e06372,
    0x1b4e8f1ece940ef9,
    0x8fba773111c36c8b,
    0xd68bb8cfb9db4b8c,
    0x55c77fc3d8bb21c8,
    0x537e51a16703ec98,
    0x5b59b882a92c78dc,
    0x6560835df0c9e50a,
    0x3313cd8e39051c59,
    0xae7a016ac5d7748d,
    0x1373684a8c9dc,
]));

// Generator of G1
// X = 23803503838482697364219212396100314255266282256287758532210460958670711284501374254909249084643549104668878996224193897061976788052185662569738774028756446662400954817676947337090686257134874703224133183061214213216866019444443,
// Y = 21091012152938225813050540665280291929032924333518476279110711148670464794818544820522390295209715531901248676888544060590943737249563733104806697968779796610374994498702698840169538725164956072726942500665132927942037078135054,
// Z = 1.
pub const G1_GENERATOR_X: Fq = Fq(FqRepr([
    0x490de480bfee06db,
    0x8fdf2825da61ef2f,
    0x8630190e5a4af536,
    0x4cbd5fb31ae7fe85,
    0x1218c2a03c852868,
    0x0f153ebc3892330c,
    0x8cbfe8583e2c58f1,
    0xfa5236a4acfe32ea,
    0x844897de2d94348e,
    0x066ba7907985270f,
    0xbea211006c9ef632,
    0x307775573b759676,
]));

pub const G1_GENERATOR_Y: Fq = Fq(FqRepr([
    0x6091211d0561d10e,
    0x4863164b0584596a,
    0x2952b1327a3a8af3,
    0xa7290ddc2fc53a32,
    0x53f88786f3e93f62,
    0x49a7ffe1e7d48d75,
    0xf05fe1ced1e771cc,
    0x51802ce070fa68c6,
    0x604644a123d1798c,
    0x170387e6066aba17,
    0xa05ed434b53dbb5a,
    0x9abfaa903c09021c,
]));

// A coefficient of MNT4-753 G2 = mnt4753_twist_coeff_a
// mnt4753_Fq2::non_residue = mnt4753_Fq("13");
//  = (G1_A_COEFF * NON_RESIDUE, ZERO) = (26, 0)
pub const G2_A_COEFF: Fq2 = Fq2 {
    c0: Fq(FqRepr([
        0x1A, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    c1: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
};

// B coefficient of MNT4-753 G2 = mnt4753_twist_coeff_b
//  = (ZERO, G1_B_COEFF * NON_RESIDUE);
pub const G2_B_COEFF: Fq2 = Fq2 {
    c0: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    c1: Fq(FqRepr([
        0x1370b34a3f4e425c,
        0xcde04fb71c7c7fcf,
        0x46bcc103a7639329,
        0x09a1a6323359dded,
        0x249ff55e1586e460,
        0xd262413a70c08a45,
        0x6ee0fe65305b46ce,
        0x63a09573523ab6c3,
        0x302763f9d581ddee,
        0xd834b5b608c4f11f,
        0x5b1d915494da7dbd,
        0x1a7934ffc1fac,
    ])),
};

// Generator of G2
// These are two Fq elements each because X and Y (and Z) are elements of Fq^2
// X = 22367666623321080720060256844679369841450849258634485122226826668687008928557241162389052587294939105987791589807198701072089850184203060629036090027206884547397819080026926412256978135536735656049173059573120822105654153939204,
// 19674349354065582663569886390557105215375764356464013910804136534831880915742161945711267871023918136941472003751075703860943205026648847064247080124670799190998395234694182621794580160576822167228187443851233972049521455293042,
// Y = 6945425020677398967988875731588951175743495235863391886533295045397037605326535330657361771765903175481062759367498970743022872494546449436815843306838794729313050998681159000579427733029709987073254733976366326071957733646574,
// 17406100775489352738678485154027036191618283163679980195193677896785273172506466216232026037788788436442188057889820014276378772936042638717710384987239430912364681046070625200474931975266875995282055499803236813013874788622488,
// Z = 1.

pub const G2_GENERATOR_X_C0: Fq = Fq(FqRepr([
    0x43ec4b2981af8904,
    0x9f572caa85a91c52,
    0x2fc1e763a5c32c2c,
    0xa04fd0165ac8debb,
    0xbfa2e4dacb821c91,
    0x474b2febf924aca0,
    0xeb07d90c77c67256,
    0x044b5cf0ae49850e,
    0xe3a7b833be42c11d,
    0x7aa11b2d74eb8627,
    0x03332835a5de0f32,
    0xf1b7155ed4e9,
]));

pub const G2_GENERATOR_X_C1: Fq = Fq(FqRepr([
    0xa3374d6439526272,
    0x7e5667038bb2e828,
    0xd186d60b4a103e15,
    0xdf5f95b6b62c24c7,
    0xa19916cf103f102a,
    0x3af1de0d5d425da7,
    0xb9e6d066813ed67f,
    0xdc78dc2010d74f82,
    0x777ad052ec5f4b95,
    0xb8e979ced82ca592,
    0xe731713182a88907,
    0xd49c264ec663,
]));

pub const G2_GENERATOR_Y_C0: Fq = Fq(FqRepr([
    0xfdd407f04be620ee,
    0x2a5200b14d6f9dd0,
    0x458f4b2face11f8d,
    0x4a359437e75638a1,
    0xd3d7e6c6c2c073c2,
    0x7ace8f1162079cd2,
    0x5d90af34d3cd9828,
    0x9e34d8b69cc94aef,
    0x5ce0f925cd5d0220,
    0x4acf17b2267e21dc,
    0x6ebbaddd2d7f288c,
    0x4b0e2fef0809,
]));

pub const G2_GENERATOR_Y_C1: Fq = Fq(FqRepr([
    0x2eaa9df68f4d6098,
    0x006b013e7afb186f,
    0x3b863d59c422c3ea,
    0x50e8bfa5375791d7,
    0x9660dd6f3d4336ad,
    0xeee53c75f55a6f7d,
    0x477909ecca358be2,
    0x520e80d31966e3ec,
    0x984c0acdc67d2962,
    0xe22f5688e51b30bd,
    0x4f6f8697cd5e45fa,
    0xbc1925e7fcb6,
]));

// Coefficients for the Frobenius automorphism.
//    1,
//    "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600"
pub const FROBENIUS_COEFF_FQ2_C1: [Fq; 2] = [
    Fq(FqRepr([
        0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    Fq(FqRepr([
        0x5e9063de245e8000,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x07fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ])),
];

// 1,
// "18691656569803771296244054523431852464958959799019013859007259692542121208304602539555350517075508287829753932558576476751900235650227380562700444433662761577027341858128610410779088384480737679672900770810745291515010467307990",
// "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600",
//  "23206834398115182106100160267808784663211750120934935212776243228483231604266504233503543246714830633588317039329677309362453490879357004638891167538350364891904062489821230132228897943262725174047727280881395973788104254381611"
pub const FROBENIUS_COEFF_FQ4_C1: [Fq; 4] = [
    Fq(FqRepr([
        0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    Fq(FqRepr([
        0x223e849befdd21d6,
        0xd1a5ff487116d9bb,
        0x7a4bd915e94ba9e2,
        0x5d4dea2714aaefe6,
        0xa7a444cff70a31e4,
        0x7d191f9222c769ec,
        0x7236eda8e40042fd,
        0x2f5ba2a0688499e6,
        0x8e9a3358e6c391cf,
        0xd3e06bd34482d77c,
        0xa98148368fbcc91f,
        0xc9fd93af6b3f,
    ])),
    Fq(FqRepr([
        0x5e9063de245e8000,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x07fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ])),
    Fq(FqRepr([
        0x3c51df4234815e2b,
        0x650df32635e4b7e4,
        0x28e0c81eb3088977,
        0x18bd0d6e37f359c8,
        0x106ac8d5d44a1f2c,
        0x33fec7e4cf509bb1,
        0x279a3730bd5ab4a0,
        0xd8a21685801c53a7,
        0xd01db5a085d446a3,
        0xe4192b7d170cd870,
        0x66a147ec5f26048d,
        0xfac899e358d1,
    ])),
];

#[derive(PrimeField)]
#[PrimeFieldModulus = "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689601"]
#[PrimeFieldGenerator = "17"]
pub struct Fq(FqRepr);

// This is negative one wrt the limbs, mod q
// -((2**756) mod q) mod q
pub const NEGATIVE_ONE: Fq = Fq(FqRepr([
    0xc5e777324a8210bf,
    0x51d0228bd2d9cb18,
    0xcbc42bd0cdafcec2,
    0xef0234cfaee99ea2,
    0xcae87111aa4ae6c8,
    0x930899ec2314e834,
    0x67c4e9228e277244,
    0xae72762315b0e32b,
    0x1e431f2d6f0b3251,
    0xa85518752329c761,
    0x7add306fcee92c18,
    0x1497e8ec9e1ce,
]));

#[test]
fn test_a_coeff() {
    assert_eq!(Fq::from_repr(FqRepr::from(2)).unwrap(), A_COEFF);
}

/*
    // FROBENIUS_COEFF_FQ2_C1 = [Fq(-1)**(((q^0) - 1) / 2), Fq(-1)**(((q^1) - 1) / 2)]
    // FROBENIUS_COEFF_FQ6_C1: [Fq2; 6] = [ Fq2(u + 1)**(((q^i) - 1) / 3) ] for i = 0, .. , 5

fn test_frob_coeffs() {
    let mut nqr = Fq::one();
    nqr.negate();

    assert_eq!(FROBENIUS_COEFF_FQ2_C1[0], Fq::one());
    assert_eq!(
        FROBENIUS_COEFF_FQ2_C1[1],
        nqr.pow([
            0xdcff7fffffffd555,
            0xf55ffff58a9ffff,
            0xb39869507b587b12,
            0xb23ba5c279c2895f,
            0x258dd3db21a5d66b,
            0xd0088f51cbff34d
        ])
    );

    let nqr = Fq2 {
        c0: Fq::one(),
        c1: Fq::one(),
    };

    assert_eq!(FROBENIUS_COEFF_FQ2_C1[0], Fq2::one());
    assert_eq!(
        FROBENIUS_COEFF_FQ2_C1[1],
        nqr.pow([
            0x9354ffffffffe38e,
            0xa395554e5c6aaaa,
            0xcd104635a790520c,
            0xcc27c3d6fbd7063f,
            0x190937e76bc3e447,
            0x8ab05f8bdd54cde
        ])
    );

    assert_eq!(FROBENIUS_COEFF_FQ2_C2[0], Fq2::one());
    assert_eq!(
        FROBENIUS_COEFF_FQ2_C2[1],
        nqr.pow([
            0x26a9ffffffffc71c,
            0x1472aaa9cb8d5555,
            0x9a208c6b4f20a418,
            0x984f87adf7ae0c7f,
            0x32126fced787c88f,
            0x11560bf17baa99bc
        ])
    );
}
*/

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

/*
#[test]
fn test_fq_repr_div2() {
    let mut a = FqRepr([
        0x8b0ad39f8dd7482a,
        0x147221c9a7178b69,
        0x54764cb08d8a6aa0,
        0x8519d708e1d83041,
        0x41f82777bd13fdb,
        0xf43944578f9b771b,
    ]);
    a.div2();
    assert_eq!(
        a,
        FqRepr([
            0xc58569cfc6eba415,
            0xa3910e4d38bc5b4,
            0xaa3b265846c53550,
            0xc28ceb8470ec1820,
            0x820fc13bbde89fed,
            0x7a1ca22bc7cdbb8d
        ])
    );
    for _ in 0..10 {
        a.div2();
    }
    assert_eq!(
        a,
        FqRepr([
            0x6d31615a73f1bae9,
            0x54028e443934e2f1,
            0x82a8ec99611b14d,
            0xfb70a33ae11c3b06,
            0xe36083f04eef7a27,
            0x1e87288af1f36e
        ])
    );
    for _ in 0..300 {
        a.div2();
    }
    assert_eq!(a, FqRepr([0x7288af1f36ee3608, 0x1e8, 0x0, 0x0, 0x0, 0x0]));
    for _ in 0..50 {
        a.div2();
    }
    assert_eq!(a, FqRepr([0x7a1ca2, 0x0, 0x0, 0x0, 0x0, 0x0]));
    for _ in 0..22 {
        a.div2();
    }
    assert_eq!(a, FqRepr([0x1, 0x0, 0x0, 0x0, 0x0, 0x0]));
    a.div2();
    assert!(a.is_zero());
}

#[test]
fn test_fq_repr_shr() {
    let mut a = FqRepr([
        0xaa5cdd6172847ffd,
        0x43242c06aed55287,
        0x9ddd5b312f3dd104,
        0xc5541fd48046b7e7,
        0x16080cf4071e0b05,
        0x1225f2901aea514e,
    ]);
    a.shr(0);
    assert_eq!(
        a,
        FqRepr([
            0xaa5cdd6172847ffd,
            0x43242c06aed55287,
            0x9ddd5b312f3dd104,
            0xc5541fd48046b7e7,
            0x16080cf4071e0b05,
            0x1225f2901aea514e
        ])
    );
    a.shr(1);
    assert_eq!(
        a,
        FqRepr([
            0xd52e6eb0b9423ffe,
            0x21921603576aa943,
            0xceeead98979ee882,
            0xe2aa0fea40235bf3,
            0xb04067a038f0582,
            0x912f9480d7528a7
        ])
    );
    a.shr(50);
    assert_eq!(
        a,
        FqRepr([
            0x8580d5daaa50f54b,
            0xab6625e7ba208864,
            0x83fa9008d6fcf3bb,
            0x19e80e3c160b8aa,
            0xbe52035d4a29c2c1,
            0x244
        ])
    );
    a.shr(130);
    assert_eq!(
        a,
        FqRepr([
            0xa0fea40235bf3cee,
            0x4067a038f0582e2a,
            0x2f9480d7528a70b0,
            0x91,
            0x0,
            0x0
        ])
    );
    a.shr(64);
    assert_eq!(
        a,
        FqRepr([0x4067a038f0582e2a, 0x2f9480d7528a70b0, 0x91, 0x0, 0x0, 0x0])
    );
}

#[test]
fn test_fq_repr_mul2() {
    let mut a = FqRepr::from(23712937547);
    a.mul2();
    assert_eq!(a, FqRepr([0xb0acd6c96, 0x0, 0x0, 0x0, 0x0, 0x0]));
    for _ in 0..60 {
        a.mul2();
    }
    assert_eq!(
        a,
        FqRepr([0x6000000000000000, 0xb0acd6c9, 0x0, 0x0, 0x0, 0x0])
    );
    for _ in 0..300 {
        a.mul2();
    }
    assert_eq!(a, FqRepr([0x0, 0x0, 0x0, 0x0, 0x0, 0xcd6c960000000000]));
    for _ in 0..17 {
        a.mul2();
    }
    assert_eq!(a, FqRepr([0x0, 0x0, 0x0, 0x0, 0x0, 0x2c00000000000000]));
    for _ in 0..6 {
        a.mul2();
    }
    assert!(a.is_zero());
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

    let mut t = FqRepr([
        0x827a4a08041ebd9,
        0x3c239f3dcc8f0d6b,
        0x9ab46a912d555364,
        0x196936b17b43910b,
        0xad0eb3948a5c34fd,
        0xd56f7b5ab8b5ce8,
    ]);
    t.sub_noborrow(&FqRepr([
        0xc7867917187ca02b,
        0x5d75679d4911ffef,
        0x8c5b3e48b1a71c15,
        0x6a427ae846fd66aa,
        0x7a37e7265ee1eaf9,
        0x7c0577a26f59d5,
    ]));
    assert!(
        t == FqRepr([
            0x40a12b8967c54bae,
            0xdeae37a0837d0d7b,
            0xe592c487bae374e,
            0xaf26bbc934462a61,
            0x32d6cc6e2b7a4a03,
            0xcdaf23e091c0313
        ])
    );

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

    // Subtracting q+1 from q should produce -1 (mod 2**384)
    let mut qplusone = FqRepr([
        0xb9feffffffffaaab,
        0x1eabfffeb153ffff,
        0x6730d2a0f6b0f624,
        0x64774b84f38512bf,
        0x4b1ba7b6434bacd7,
        0x1a0111ea397fe69a,
    ]);
    qplusone.sub_noborrow(&FqRepr([
        0xb9feffffffffaaac,
        0x1eabfffeb153ffff,
        0x6730d2a0f6b0f624,
        0x64774b84f38512bf,
        0x4b1ba7b6434bacd7,
        0x1a0111ea397fe69a,
    ]));
    assert_eq!(
        qplusone,
        FqRepr([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff
        ])
    );
}

#[test]
fn test_fq_repr_add_nocarry() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let mut t = FqRepr([
        0x827a4a08041ebd9,
        0x3c239f3dcc8f0d6b,
        0x9ab46a912d555364,
        0x196936b17b43910b,
        0xad0eb3948a5c34fd,
        0xd56f7b5ab8b5ce8,
    ]);
    t.add_nocarry(&FqRepr([
        0xc7867917187ca02b,
        0x5d75679d4911ffef,
        0x8c5b3e48b1a71c15,
        0x6a427ae846fd66aa,
        0x7a37e7265ee1eaf9,
        0x7c0577a26f59d5,
    ]));
    assert!(
        t == FqRepr([
            0xcfae1db798be8c04,
            0x999906db15a10d5a,
            0x270fa8d9defc6f79,
            0x83abb199c240f7b6,
            0x27469abae93e1ff6,
            0xdd2fd2d4dfab6be
        ])
    );

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

    // Adding 1 to (2^384 - 1) should produce zero
    let mut x = FqRepr([
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
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
    assert!(Fq(FqRepr([
        0xdf4671abd14dab3e,
        0xe2dc0c9f534fbd33,
        0x31ca6c880cc444a6,
        0x257a67e70ef33359,
        0xf9b29e493f899b36,
        0x17c8be1800b9f059
    ]))
    .is_valid());
    assert!(!Fq(FqRepr([
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff
    ]))
    .is_valid());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let a = Fq::rand(&mut rng);
        assert!(a.is_valid());
    }
}

#[test]
fn test_fq_add_assign() {
    {
        // Random number
        let mut tmp = Fq(FqRepr([
            0x624434821df92b69,
            0x503260c04fd2e2ea,
            0xd9df726e0d16e8ce,
            0xfbcb39adfd5dfaeb,
            0x86b8a22b0c88b112,
            0x165a2ed809e4201b,
        ]));
        assert!(tmp.is_valid());
        // Test that adding zero has no effect.
        tmp.add_assign(&Fq(FqRepr::from(0)));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0x624434821df92b69,
                0x503260c04fd2e2ea,
                0xd9df726e0d16e8ce,
                0xfbcb39adfd5dfaeb,
                0x86b8a22b0c88b112,
                0x165a2ed809e4201b
            ]))
        );
        // Add one and test for the result.
        tmp.add_assign(&Fq(FqRepr::from(1)));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0x624434821df92b6a,
                0x503260c04fd2e2ea,
                0xd9df726e0d16e8ce,
                0xfbcb39adfd5dfaeb,
                0x86b8a22b0c88b112,
                0x165a2ed809e4201b
            ]))
        );
        // Add another random number that exercises the reduction.
        tmp.add_assign(&Fq(FqRepr([
            0x374d8f8ea7a648d8,
            0xe318bb0ebb8bfa9b,
            0x613d996f0a95b400,
            0x9fac233cb7e4fef1,
            0x67e47552d253c52,
            0x5c31b227edf25da,
        ])));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0xdf92c410c59fc997,
                0x149f1bd05a0add85,
                0xd3ec393c20fba6ab,
                0x37001165c1bde71d,
                0x421b41c9f662408e,
                0x21c38104f435f5b
            ]))
        );
        // Add one to (q - 1) and test for the result.
        tmp = Fq(FqRepr([
            0xb9feffffffffaaaa,
            0x1eabfffeb153ffff,
            0x6730d2a0f6b0f624,
            0x64774b84f38512bf,
            0x4b1ba7b6434bacd7,
            0x1a0111ea397fe69a,
        ]));
        tmp.add_assign(&Fq(FqRepr::from(1)));
        assert!(tmp.0.is_zero());
        // Add a random number to another one such that the result is q - 1
        tmp = Fq(FqRepr([
            0x531221a410efc95b,
            0x72819306027e9717,
            0x5ecefb937068b746,
            0x97de59cd6feaefd7,
            0xdc35c51158644588,
            0xb2d176c04f2100,
        ]));
        tmp.add_assign(&Fq(FqRepr([
            0x66ecde5bef0fe14f,
            0xac2a6cf8aed568e8,
            0x861d70d86483edd,
            0xcc98f1b7839a22e8,
            0x6ee5e2a4eae7674e,
            0x194e40737930c599,
        ])));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0xb9feffffffffaaaa,
                0x1eabfffeb153ffff,
                0x6730d2a0f6b0f624,
                0x64774b84f38512bf,
                0x4b1ba7b6434bacd7,
                0x1a0111ea397fe69a
            ]))
        );
        // Add one to the result and test for it.
        tmp.add_assign(&Fq(FqRepr::from(1)));
        assert!(tmp.0.is_zero());
    }

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
    {
        // Test arbitrary subtraction that tests reduction.
        let mut tmp = Fq(FqRepr([
            0x531221a410efc95b,
            0x72819306027e9717,
            0x5ecefb937068b746,
            0x97de59cd6feaefd7,
            0xdc35c51158644588,
            0xb2d176c04f2100,
        ]));
        tmp.sub_assign(&Fq(FqRepr([
            0x98910d20877e4ada,
            0x940c983013f4b8ba,
            0xf677dc9b8345ba33,
            0xbef2ce6b7f577eba,
            0xe1ae288ac3222c44,
            0x5968bb602790806,
        ])));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0x748014838971292c,
                0xfd20fad49fddde5c,
                0xcf87f198e3d3f336,
                0x3d62d6e6e41883db,
                0x45a3443cd88dc61b,
                0x151d57aaf755ff94
            ]))
        );

        // Test the opposite subtraction which doesn't test reduction.
        tmp = Fq(FqRepr([
            0x98910d20877e4ada,
            0x940c983013f4b8ba,
            0xf677dc9b8345ba33,
            0xbef2ce6b7f577eba,
            0xe1ae288ac3222c44,
            0x5968bb602790806,
        ]));
        tmp.sub_assign(&Fq(FqRepr([
            0x531221a410efc95b,
            0x72819306027e9717,
            0x5ecefb937068b746,
            0x97de59cd6feaefd7,
            0xdc35c51158644588,
            0xb2d176c04f2100,
        ])));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0x457eeb7c768e817f,
                0x218b052a117621a3,
                0x97a8e10812dd02ed,
                0x2714749e0f6c8ee3,
                0x57863796abde6bc,
                0x4e3ba3f4229e706
            ]))
        );

        // Test for sensible results with zero
        tmp = Fq(FqRepr::from(0));
        tmp.sub_assign(&Fq(FqRepr::from(0)));
        assert!(tmp.is_zero());

        tmp = Fq(FqRepr([
            0x98910d20877e4ada,
            0x940c983013f4b8ba,
            0xf677dc9b8345ba33,
            0xbef2ce6b7f577eba,
            0xe1ae288ac3222c44,
            0x5968bb602790806,
        ]));
        tmp.sub_assign(&Fq(FqRepr::from(0)));
        assert_eq!(
            tmp,
            Fq(FqRepr([
                0x98910d20877e4ada,
                0x940c983013f4b8ba,
                0xf677dc9b8345ba33,
                0xbef2ce6b7f577eba,
                0xe1ae288ac3222c44,
                0x5968bb602790806
            ]))
        );
    }

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
        0xcc6200000020aa8a,
        0x422800801dd8001a,
        0x7f4f5e619041c62c,
        0x8a55171ac70ed2ba,
        0x3f69cc3a3d07d58b,
        0xb972455fd09b8ef,
    ]));
    tmp.mul_assign(&Fq(FqRepr([
        0x329300000030ffcf,
        0x633c00c02cc40028,
        0xbef70d925862a942,
        0x4f7fa2a82a963c17,
        0xdf1eb2575b8bc051,
        0x1162b680fb8e9566,
    ])));
    assert!(
        tmp == Fq(FqRepr([
            0x9dc4000001ebfe14,
            0x2850078997b00193,
            0xa8197f1abb4d7bf,
            0xc0309573f4bfe871,
            0xf48d0923ffaf7620,
            0x11d4b58c7a926e66
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
*/
#[test]
fn test_fq_squaring() {
    let mut a = Fq(FqRepr([
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
        0x19ffffffffffffff,
    ]));
    assert!(a.is_valid());
    a.square();
    assert_eq!(
        a,
        Fq::from_repr(FqRepr([
            0x1cfb28fe7dfbbb86,
            0x1cfb28fe7dfbbb86,
            0x24cbe1731577a59,
            0xcce1d4edc120e66e,
            0xdc05c659b4e15b27,
            0x79361e5a802c6a23,
            0x24bcbe5d51b9a6f,
            0x24cbe1731577a59,
            0xcce1d4edc120e66e,
            0xdc05c659b4e15b27,
            0x79361e5a802c6a23,
            0x24bcbe5d51b9a6f
        ]))
        .unwrap()
    );

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
        0x5e9063de245e8002,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x07fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]))
    .is_err());

    // q should not be in the field
    assert!(Fq::from_repr(Fq::char()).is_err());

    /*
    // Multiply some arbitrary representations to see if the result is as expected.
    let a = FqRepr([
        0x4a49dad4ff6cde2d,
        0xac62a82a8f51cd50,
        0x2b1f41ab9f36d640,
        0x908a387f480735f1,
        0xae30740c08a875d7,
        0x6c80918a365ef78,
    ]);
    let mut a_fq = Fq::from_repr(a).unwrap();
    let b = FqRepr([
        0xbba57917c32f0cf0,
        0xe7f878cf87f05e5d,
        0x9498b4292fd27459,
        0xd59fd94ee4572cfa,
        0x1f607186d5bb0059,
        0xb13955f5ac7f6a3,
    ]);
    let b_fq = Fq::from_repr(b).unwrap();
    let c = FqRepr([
        0xf5f70713b717914c,
        0x355ea5ac64cbbab1,
        0xce60dd43417ec960,
        0xf16b9d77b0ad7d10,
        0xa44c204c1de7cdb7,
        0x1684487772bc9a5a,
    ]);
    a_fq.mul_assign(&b_fq);
    assert_eq!(a_fq.into_repr(), c);
    */
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
