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
        0x5e9063de245e8001,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]);
    qplusone.sub_noborrow(&FqRepr([
        0x5e9063de245e8002,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
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
