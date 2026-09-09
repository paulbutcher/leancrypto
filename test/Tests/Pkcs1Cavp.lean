/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Tests.Cavp

/-!
Every case the NIST CAVP file `SigVer15_186-3.rsp` records for a 2048-bit modulus with SHA-384 or
SHA-512, from `186-3rsatestvectors.zip`. `Result = P` and `Result = F` become `true` and `false`.

Thirty of the thirty-six are failures, which is the proportion that matters: a verifier answering
`true` unconditionally would agree with six. The SHA-256 cases of the same file, and the forgeries
that appear in no published suite, are in `Tests.RsaVectors`.

The response file writes each field as a number, so a message or a signature whose first byte is
zero is recorded one or two digits short. They are written here at their full width instead,
because a signature is an octet string of the modulus length and is refused at any other.
-/

namespace Tests.Pkcs1Cavp
open Leancrypto Tests.Cavp

private structure Case where
  digest : Sha2
  exponent : String
  message : String
  signature : String
  expected : Bool

/-- The response file states a modulus once and then several cases under it, and so does this. -/
private structure Group where
  modulus : String
  entries : List Case

private def groups : List Group :=
  [ { modulus :=
        "c858aea188541c0dd2626eec9a8c98511ca03870353128c1687d94a1be762a49" ++
        "40fca789831a720e108f2f7c1fc20aab38336b5668205d62963c51aad7475718" ++
        "3faae7c0c59b9f679e96393e7f93e8a30ce99fed1b8e85e7146bd69a3f8dc573" ++
        "4bbacd51359f4f66aa507fbf4e69708877f7cd7cfb6868006e330869d9eee99f" ++
        "466962b0dee9080d9413bdec2e41445190394a49ecb191167350be411cdd6ade" ++
        "4eb38c4c4bf891b43c91b5981a3bcc8a66f85e5cbaef751e3cbe94c7f193fd78" ++
        "ac55048800250d5cc9e41b89319ac3d0258aa640299e165b0cf7e5e108f76a12" ++
        "f72132f6a2a4c239df0544d3d8407b94f9f38e9156c825a7eae001543fb264eb",
      entries :=
        [ { digest := .sha384, exponent := "2a26db", expected := false,
            message :=
              "6c1c4396f7b7f9228e832a13692002ba2aff439dcb7fddbfd456c022d133ee89" ++
              "03a2d482562fdaa493ce3916d77a0c51441dab26f6b0340238a36a71f87fc3e1" ++
              "79cabca9482b704971ce69f3f20ab64b70413d6c2908532b2a888a9fc224cae1" ++
              "365da410b6f2e298904b63b4a41726321835a4774dd063c211cfc8b5166c2d11",
            signature :=
              "422e70ace2a2c07d2adbecd9dd5714c42d0e768d48bc33fea822974e42ecf99c" ++
              "791276e44936e70b183e712e0dd9b484199b92f24a76c6908faf6bc20fe266fa" ++
              "03886781cead7c82aeeebdd150bf48ae4698e76807ef24d29f3cd5590395f472" ++
              "5dbe7e468540b4d4d8be84e673bff86b0c08af17e738af91cee4f14367dd6bed" ++
              "f71b5e8e148b61ea968f16160604834831d557879542598be7d2fd01c7966f0a" ++
              "e1ec2554d8dd653f20c551a1de6212481e2a19a3e2fa9cf005e5f3ee1962c34e" ++
              "3e85f84104f9172debf89db438c32f2a8061ac15d3cd3f3a6b7d75fd7c3f8ea0" ++
              "c505c6398d1e70eb12e9e16f5a0e4b459c02ec38f0dfc7a4a3139c1fba6f59b4" },
          { digest := .sha384, exponent := "2a26db", expected := true,
            message :=
              "d6a169031049b0b3b582d22bf40b9fca45d2618457146c2b4ac6f6ed1f34291f" ++
              "6de8773955cd2e21b7944caca65794621a7ce181e5ddbb45e9252867877dc4e3" ++
              "5b6914ff26ec18890bf31f60fff1df367bc6c59373e58a1d8cb607188a394a29" ++
              "07ede95f6bf096731867f44fe520aacece76b5c3ea75023c9d3f3c080eaee376",
            signature :=
              "b9794f252e6907dc4c41de42ea5a0e6361114ac3814c4a92583ca70fd78e9819" ++
              "0a0d9215bd5282e8520422093eff2e1cfa335cffcdcc27fe9bafe4516e74445d" ++
              "4aa17a08db754fc69b156d86ff26eb9e814f605142a3051d2fa64305d3e5c5c5" ++
              "f67c7d9e38c5054d069c14b23e4278fa5a73381f61f90a9ec428c883f1366e27" ++
              "ec0219db8c942582a284c161eead307285d0e4df6b0d7dea0e8216d7ef2e4b2e" ++
              "de2296e0b780e5a3f8d15f123f737b9d6170074f758de32b6f1e958b27e422b0" ++
              "53df8f5fbbbafbc14119260f7022cd2934e8faeffbd7085aabc44497bfe07387" ++
              "bc0e5aa02399eab99318adb98f99a677aa0683e0c11d638cb13907fc5c3147e5" },
          { digest := .sha384, exponent := "c74c01", expected := false,
            message :=
              "eab87ecf61ca1ea8eb29498b510ab371784d0274e2fa77e077ebd18c86c66e6b" ++
              "072fb45e233baf4cf627fb75934ae5034848cde22489cfd2b7e9a2bb19b1bf40" ++
              "2ec7c69627211e974c7fdc12f95ae766e717594fad8128ff8776057155e084fa" ++
              "e7e87e217766b4b0779bb40b8e2201c1dd246e6186cccb8f6ffac356433c05c0",
            signature :=
              "35720e6883452e78bf0f9ba1566a638c8f5060a8ee313ba66bd2496d67b78d01" ++
              "fa1d5bcd4e3a96aebe6b0e66480335a49a500abd126c5b1beaaa60135db4e51b" ++
              "4efb5a59b662ad3525c2dd1c867bcf609971806895550531d9f5b0ded79f804d" ++
              "1d63c4a00931a64244a2b5f004287b523e9bd23a3ae8b393d2607d1a83506228" ++
              "2477c2441cf3176110fa0064350f2cf73b7c67e02bf498eff69161e62e514563" ++
              "d23385be16498c525967350e047392861b7040c9b4039b5a8a49eddb385aaa45" ++
              "93c14e20dc4aa2f67258290a51c6e836e83edc061d4bcf5b8f3db470068372ff" ++
              "76a0109be686c25e70638d15156845dfb8ca1e84d0aef538798014ae1c173a14" },
          { digest := .sha384, exponent := "2a26db", expected := false,
            message :=
              "fd73237a3010d505ea0ca786c5a3ae4d20c4eedbc6232199ce8ab4c9bf6f13bc" ++
              "f8cc26454f2b1b6ff900676baa3c07ccfc1f0cf7154e56d48425a0ca6d4ebdeb" ++
              "e693206ba0f0a257caed8083322ba3c5ae3c2560bab710c3628c697463966d47" ++
              "8d6f1ad36b88f1262679fbb8a7950a9efcc24100fd88d6cd2f6717ade86eab38",
            signature :=
              "192d8fe5a69a1f9acf186f42893e458b6356b10a8fd0ee45114acf625b61c69d" ++
              "13884f7860b02acd67b5b5082bce20815e384dee608162fc9d19ac977842018e" ++
              "4b3f321d84bfb487c0f4f6a465b3f296c73ca3d8817c771c9969ae1144b1abcf" ++
              "6de251e504d1f662d6094d4e6fcd9ea3f85162883e1179e9fee4a3d7daf95bba" ++
              "dc64221fdc8c144fb4ca502f3eb11df85fe6bba561feed191963ff9f8441b583" ++
              "bd84ee540e47b318629ad59a251b759f060a40e717e50d9c0c0eb43122e65945" ++
              "75725382684c65ecf7f27e42c3e1f7d95c657371978772e111309bf4bae5241f" ++
              "adad0ad9cbd04ebcc8ee76b368439be21493aa41549dac8c356e65435f706d79" },
          { digest := .sha384, exponent := "2a26db", expected := false,
            message :=
              "c17eda0010c4add3f0616155cbe6d43f90568851052d9e825fa002591027e39b" ++
              "e03966263f569b1dd94bb0456cb264afd6b8bf987323008da593d8d3b407d505" ++
              "d9a421ff95b26cfb47e827fafee9f3668c0e59f5dc66bbd085fb8af59e57bad9" ++
              "d5477352bbdf0ab562be2f3b2a9468aad8e1be31e8ffb59325628288761f7960",
            signature :=
              "669f6c902798a9c91672addb4fd138ca41ba9b5fbc8efab9bed5e7e25662a40a" ++
              "f734240a301d304134e75494ba961740aa6b9fe54a340851791726a864a2d164" ++
              "5daafcbf38f49a5b319ab86101ae4fc5f21b0f15cd12e7979b6e3b2fb61dd049" ++
              "f9d864160110a68cbb9d399eddde358571cfad48f2057dcdf324768d8d3903d0" ++
              "a861a5824ff3a5b715fb7a098a41624ad13219a0af11eaced337e8e8aaf926eb" ++
              "4ad60534422ff986bfb498c63cba0cd6ccea9018a96e9a41e4693586aa70a0d6" ++
              "dc5c6312418d63e9f91aaf5df8d01dcaad7335cf88badf6d8da7fa9cd83e32be" ++
              "840f1b2cca1c8103d73d8a9949d72b4b8c56eb7fbfc523dc1accf80de1023d8c" },
          { digest := .sha384, exponent := "2a26db", expected := false,
            message :=
              "92c641b80aa222fad6c757ad0a8936e0459bf8f4367f63ae5f41a68a19658452" ++
              "d91eb4f0b1c188811a78ceaaf03bf42fbefc6fc13c225c1816396842efe8ee3b" ++
              "a62360bdd8a1e859a6914fc7b8891d7b81bf0278c57b746959cc9aee2b7b6934" ++
              "823d0dc8862c8aad0278a3ac695afbeb174a7ac1da72f2c9b1620235d3053b65",
            signature :=
              "5135f98250db1ebbd738c4d905db5a395c36c99f929d6cbe5bb4de9288575ede" ++
              "d2b14220ea49ca7cd04584067b000964df2a4cf0b185b7a080c14ae05cc277b8" ++
              "751b2f1fc061de93b429fdef99c39704a158a5463041a109614c9bb1c9f66df4" ++
              "8a67af779bfe85e179f289cca20d5618bda9686c0826ae14f8c86acf28645c5c" ++
              "28613446f202bc952ab1ae4aa06391edb0eb5355712b43d12ff96548292bfa07" ++
              "2ff2411e7f9d57e3fc35a43c36743b4a384150f34059c815dbcb26f55da2be86" ++
              "ac5818e2a315a12f01b98e5e7b03a67cb4056a803be2280138d1611a2667c18d" ++
              "4b2a82aff86d9fd21568b2e6575b8e3c0470da8b2d7d6d0a2a172e6415a1b7d2" } ] },
    { modulus :=
        "b6515048e1f7a3506d6bf028ea0516592078a2ebd6db04af6040bb5dde888878" ++
        "7e1fd973b1d160da25ba9095450d866625aeb7cf684b522af4edbc20adfad09e" ++
        "9c4c42919b7691e1404afe8815f229001bf7f8e2b1c511d56207972e3efa588f" ++
        "04f7bea82b64c45bc28bbc5e3ca3b1be8652c54a3393e95a58c78c34c7c7ceec" ++
        "a983e91920467d184ecd5aad0114f83d0517e6ee82944cf134e9efdb68f14322" ++
        "517acc10285c892c94e6892c9659fb85af6d11322df94edeb77a379e97c7608e" ++
        "5d23c89b56a722b54d91f0811855c21e0c41ed362ae144e2f46eebb97a9057c6" ++
        "73ddccc0f2ce178c3af086d1f93a092a2ae58bb0703ca66318913e69e36fd997",
      entries :=
        [ { digest := .sha512, exponent := "662f3b", expected := false,
            message :=
              "e5b327e067ed7a242749d21d78e0b1d68d288595dec82a55cdaab1768a5260b4" ++
              "346ff95641b040a71fd9b7aa1b16ac0a838f7550073cfb5865fb750646e07635" ++
              "62cc2af0eb41dce52974bc1662a4e0d2fcab88e4e5d3a60a33ea9ea908994abe" ++
              "b9f141182f4759c58d426aca1232551742a345b9403335527fa0b3c69925e338",
            signature :=
              "488df2a0a8775e6e65c6f457cb9e29dcc8ab6c37a12cf820308732052bfe068e" ++
              "3c6f3c4e73c17615aa6319b76d62df6cf48378b834dc412b9e5875f7fe16bb26" ++
              "70c4ee51cdc259df813d5faa541472581103421a9718e79b8c671b1c7b50f6d4" ++
              "315b96423ba6aca9d060a32372c4c237f02eef44f54f872bf91b5a390adf9c5a" ++
              "7a884416add7d15afd8fb8073243dd587ac8011a88d5566cac84d5dc4ca3f2d6" ++
              "938e0d03a9e8d016b4aea22183425c2bd4696d85501e264bba7dd980c3ac45d7" ++
              "7a363955565f4675c5246802abc015236d69005d164c0f18a666d43442902be3" ++
              "8fcc381ffb6b5a046af05686b0ad32b25c1e2d82707797016ee63fc9a952d2d5" },
          { digest := .sha512, exponent := "a3e187", expected := false,
            message :=
              "6b7450077038ca8478e7a380292151ad413c1949d78076efe497beb4013f036f" ++
              "7242375864a894d5732b3b906feb1ccd606315fbc79c5e8827a024fac432743c" ++
              "abbc5b35f2894c9f4134c1179261257034aaf24d16dd17ef42649c4ba8048860" ++
              "1dcb03c7a343b88cebec7d3c18e9363fc6faf6684baa68cb3cca6ecf341d0784",
            signature :=
              "1933ff9ae5c520efeb711fd17a571a209c2ba9e0469e39a5341a70ca46c6deb2" ++
              "359005fb21c9e914e8a5037345906204261476427ddbdf29212d84c6e4e1dbda" ++
              "61aeb21ceddad1c3789d99ea28ebf72c4fef790f838191b30587e00fa841d63b" ++
              "febd00bf468b462ae935eaaef2f83ad596b29a0d538ad99b44d615217f0643f0" ++
              "d9bd755fa281e35bedca37b238a89b78f9d911a24c40ab3cf69dade4ce4a30bd" ++
              "3104f890a6cf410a1e76e625e28495f6f9b385d698e6f8a6eadf0df3af03b3e0" ++
              "78f4b0c984bddf525f220635cb2993b72ccae40ad3378cdf775431c2ceaa1aaa" ++
              "57f355eefffc0f34b5d70d1a41aac9b052594f0132308b0e329e34c0d2fdc519" },
          { digest := .sha512, exponent := "a3e187", expected := true,
            message :=
              "8b618f6669b9f0450a57cdc57f5dd0bfcc0b4812e1e2c2eacc09d9422cef4fa7" ++
              "e9325c3f22c0450b673c316929a339dd6e2fbe10c97bff198ae9eafc32413370" ++
              "2a9aa4e6b47eb4c621495afc45d223b3284d8360fe70680359d515aa9ea02e36" ++
              "b5610f61053c6200a047f186ba33b8ca602f3f0a6709272fa296025258556880",
            signature :=
              "ac87aad4ce85038b8552c4a6e93ed94368bb3376ce17ba1d08812e004b43a952" ++
              "e27fc50daee8929094e747dfbe02584a7654d950d21700605e699561c03e64d2" ++
              "016404da7b9c0b0011ff64f206225db1c8b5f974bbeca720a7c2ec73e6fbf58a" ++
              "dcc6f5cc24df6d09ade74416f30df70c4449820f24378b90c176f65651ab1c1f" ++
              "c82d3fe834e7b66d0daea47b8d1931a81d1fedd4e6996c56edbe496fa237fbd4" ++
              "1876a460780100e4e6f0864b6f9282abae4ecd98630548b5cb42e66cf9eb890e" ++
              "0651f159f356283af40c02913d2f3bbf6d8ebaf6b7d88e6699f482d7825428cc" ++
              "b7ef8129dbc665bd4df8e9a07c339a1134e907e439d0846480ae6c888c1e9be2" },
          { digest := .sha512, exponent := "a3e187", expected := false,
            message :=
              "e2a14fdf10cbe13b0afa4294d073af00b19f02c2786987c9e3e80c79573e37ae" ++
              "d1c01dfe20570f3f5225b7496c6c65fd5eaca387350c0fdf93fb6a965c17eccf" ++
              "b34eda8c25435b2b23f38830b698c2446ece487e9cf408e2c0d5b62745871cbe" ++
              "6c94b10f87586c0667aadace17bf6fdccb4a1a3013e81bd754bc19b579566f81",
            signature :=
              "0e340359f9f1fc5e974d8ad8c189efdb2849ec93994b152e497e15289015d915" ++
              "014c73503bc69b83803dfa9d8216181fcdc64782c27fe9d464ce12359aa60b44" ++
              "618119df19a8f5defcaa171c44c0c0ebe1991131132aab4b19c02438b0fead22" ++
              "bb34e51bbd565665583bb6eba36e82068e2e3040a177dab3c1d3a6f81d0a3901" ++
              "a934c10e2abd73e8b9ef7a1be29a7fe18b304ce57d073f85b1b6873ab6b8ed94" ++
              "d5a0a0f3e5fc9b4857aed36de4ca72deac235861297fdc51fd9553eed1893359" ++
              "35f23b4058f293c8cce8bd9bfc8fbb374ecf4eaa0f2a1f06ccea4ff3071beff6" ++
              "9d70efbe07513ef0bfa02dc2c6b19b5ced674a16b6672b6e04a32ae14157fe10" },
          { digest := .sha512, exponent := "a3e187", expected := false,
            message :=
              "fb200350b60d1e9b4a3b1b4d7341c55c635bfa791569a438de3bec72450baae8" ++
              "144b1f28afa2e6b5a5312862851a10fff3437e37fa5700b9a40efe96c8af34ea" ++
              "24d365bfab6b4e2e2004dac7e44a94340dcb6118b7fe6f3d9f8469efeeadeda3" ++
              "523e3fdd53723f50e53e984639d93b42d97c0ce4f467da0ef62495455c0fbb5a",
            signature :=
              "624183bf2abdb79689a45158a4876a352b19077de88aad06fadf3abcf4d2683b" ++
              "126fbf84c01ef614448c63e8a78d1e8749fd89a9b2550078c18989fea591c2a7" ++
              "c47e6a0bb4491dcb1868a43e75351ae2a7afe27782195f453bbf10643e6c3a23" ++
              "c01f2e713b6ded81e1db7ca4ecb3554fa9ae8005b80316cacdb4530a66dc2a07" ++
              "3ec494bc3419df2f275db5a33871d0a8d9cd0d8bcf90aa24f096a79a4c8f5c0d" ++
              "fd8b1887535e59079c974f87d26bfeda7022399685748414df842ce04783b6f5" ++
              "7bd2a2dbbe2e225f89c764b9775d7721157498446ce3d613332ea2cc589f7043" ++
              "afe3cae32b779ea8f1ab22fef99f67a0720306dcdf2d2cf7b35b0bf3630e03bb" },
          { digest := .sha512, exponent := "a3e187", expected := false,
            message :=
              "64ac0940e3926d11b78494ee758ee6e7f9f034ddb622a99f4a15fe5355bcee18" ++
              "8ccbeae909bf0dc4e51e520c0900052d41ce777e934af66bcecffcd365daa7af" ++
              "7eca69f547e401bc899aaaa07f0d9268e8d08de65bef0b1fdb3048acab98c260" ++
              "6331f02b440b313ec98103707ebd75e1157fdfddb719d00398bf48a6cefd2773",
            signature :=
              "3853af577c8f5f96cdb01de108ef8737886118ded95a315a5f2c34ae22f8fed6" ++
              "aad5cc1debcffa3576cc0a5050f572cfd171413275254455f19312054f06e9bc" ++
              "50f9d2dcdd1fac7ff2fbf456c2c9a1217992acbce6f867b48291911de8dcbde4" ++
              "e0b85a92536157d939dab1a42fdeeac9b15e5ed3ca542d1cab43aae3723349e4" ++
              "05f998705fd0edb19d9f4631e6c7cf7ad1962e99fbfe11629226a634eacc2ec2" ++
              "bf3ee2d87c2f6fe934a2293f5ff81b4dbeab62eb4d94bdb4ed481bcc4bf400c2" ++
              "050faade7375c811967596ab5415cc6f60fb6169faa95303ceed5ff261a93e0c" ++
              "2a2eb657501db9866fe858694f57ba25ec2f514d8f75980247597a006ab3df80" } ] },
    { modulus :=
        "ce30e07f34619a8a127f0e4401055bbea222f7c9eca47e0ace1d2adf756c0600" ++
        "f88aa165117a6f069746facb76a74ce4769d308669bc7d200763a2919ff119cf" ++
        "e6ec2a614f1bc8d4c4620921b1e60012fce58b39b19ee72ffd76544469d5e996" ++
        "215582fca819b7d6107224c6de0439918702e2de1fdf820b0900d38928877926" ++
        "fe8713f6a81be084cf0f43b7c8b16d065817855ff43a0c453ade8431b6cedf70" ++
        "0733853cf534db64e1b7e9cd25f315fe2b66121829356d502d5c833a7240ba27" ++
        "b2eef11cc4943f3f483ae31e5bb9f4006418319520d2baf5821d740bb7ec2df1" ++
        "f573f3fc89ef27090453f9bec58dc0fe8544ad9a6b157fe5183136bc768b39cf",
      entries :=
        [ { digest := .sha384, exponent := "ee7f0f", expected := false,
            message :=
              "594007ec8417ba706089919c0659195a06e8fe38094ccf18b5a10028d1a43515" ++
              "aa7ebe7cb5dd5da2754950649fb68b717d5546b690b0b71a79f6216c1a930d99" ++
              "f804d723e3ea6dceda5d549d2982ecfcd460f43f38ef504bf0720a93f6079847" ++
              "0a7d5dc75865725e556ca52deae8c265d4b012ba4b312214e1bec587ae285c85",
            signature :=
              "25c7ab6e2f2365bf872dbf31ccf19239ca06542a9fc8fc47c69d25476db031d7" ++
              "869d3a340e1e0a8933fc36b36c49a4ef34af62e53bde304a4ea28fb14e20b378" ++
              "5a543a05bff10c4572753267179b45e32ca403c1e60a49e15086e160b006cbbe" ++
              "dd908854e271e5a72c1695411da6078c6157d1d929d1b9be091c41f30f839de4" ++
              "500162ecb8507ae963c0fee43e6a431b7724fa0286d1f34f67f6e41cd6880aed" ++
              "d38c4261e43223eeadfa7d7c21c4ec3a47d04cd2fe5184180e4fb53091b7968d" ++
              "f377fe09f02f9fb9ecf4ad929b373c131628fe07296dff3b8c278f50ea61dbb5" ++
              "c1023dc311e67b45e2986ed4121eeb6a345ba4c32eedfdd76e78a036414b1839" },
          { digest := .sha384, exponent := "ee7f0f", expected := true,
            message :=
              "fa742374566394a67041b2671ea19204ca568b0c1588f605c008335dcde1eda4" ++
              "e1309ef8ed3555c00da9b79db152439dfad6dbb267cd8063b0195ec2f27a089e" ++
              "0d5d04f94af58abc428d89aafb1deb93531b1acaa293c3d99b7ada727340dea9" ++
              "46a45e61b6ccbc04d59531784528114e9dce503c0f0546cd48d3af57985af62e",
            signature :=
              "01c7c3dbf4d817f4c473b23477df5ce1de19da551dbfbf3bc2d1d5ccc0cc0e92" ++
              "b047bde1f953f7bd0617850f9fc9fb6df97cafb51f123006ebe6271e5ebdd9e5" ++
              "a78d3a537c723fe512dfdefcb424caa8918d3c1949e8f495e01ba3c74be7bcc0" ++
              "72f9f9708b08d15380d5829553c586797bd8d6879fa705511e5f8471df0eaaa9" ++
              "fa257fa867bb2bfbdeca0d7e333e4551fe9d7fe0d933397b33ecd261ad3f0f2a" ++
              "387be15b86916b18a3c96a782aedca04b9d04c8fe40d6ad607e20d29190ea971" ++
              "14d42b21a5b852c5c60301525f59345e648e2f6729b5f28ac43db465e3538f27" ++
              "9c0759ac5784cc0ff8e5c6d667465af27257718029c94ce06665562108a8ef93" },
          { digest := .sha384, exponent := "ee7f0f", expected := false,
            message :=
              "27291335228e1da94acb8a3b47f7e1e581e7763a88ffeae4b248f55006c363a8" ++
              "58fd5d02b6e4ead703d9b6b6e2061139d6f23a39a752de3e0723dc3975f54b76" ++
              "628abecc929fc617c60ab9e89805b27aa6cad9e8f260e59e89b4df0d63eb28a4" ++
              "8bf7bdfb7f68ba51da851d38309ccd8f3a96dbb133ce07ec81248635984d0219",
            signature :=
              "017fd9586eab20cfa751dfc278b426ddf05fc29d0c51d1de59f1adc1aacef5c3" ++
              "1abd2c5491994f5884f7b6e939c238ba61a25c647eb881d34cd21e99fa44f778" ++
              "db68268b46dc6e7f06dc36f28d9d96706e8e3c02bb2d6a7bf11c8fba3b747769" ++
              "7ed5f43ebf109c3f6a70ac2af0510d91ed7312c131fabe48df9ef57896598264" ++
              "9a3aedee8e103845d2ca72f5ea5f33f5f72a191e280f732cfc4d2cbd32981f38" ++
              "5518da19755bae7c90d398c15e75492391c4bc06e61ac883ce397ff2a464bba4" ++
              "32c3baaf65a053446d6d2b98f15243c00f2b248fcbc3ca46fc732f7c1297ed34" ++
              "6a80b93758ab55bf32f8bfea9eb791c26b642ae085321831c0f1df200adf3afa" },
          { digest := .sha384, exponent := "ee7f0f", expected := false,
            message :=
              "7a55bdcc36e6ff6c685ac6e7c3250a6c881aa37c05dcf6fc5c95d38985ea9e0b" ++
              "962ead8d42d5f24ca02cda0d2e4874b4163cd613b090bd0047ee73aa201df62d" ++
              "b83456634e075ffda1e678d3fb87cb796e40a6135e79216a4062023fa0e1dddf" ++
              "69cf80f761638eaaf3ee69e131c955e2198cdb2517816c62cc5947ef0e1d9d49",
            signature :=
              "54807d1b14852038dc94c53e2bb8bea76f074fe33897ded6222b52f1ff0c9144" ++
              "ebcb38d83b70f6b2d59600ef9ad089d4e3ad1ed35cda4fb54213b3e4b7b29d5f" ++
              "18725a03e9a9318bb56d96d9538013b110e7d810980aec6a451b52330e7d7f8f" ++
              "e02bb29519ea98053cbcdaa8d3657c0de6a4d268dabb6536d050de9526a03b24" ++
              "2ca9f30e7889088645fdb0e46ac09f8a7bd79914ed5873fcd66137f93e19a5e1" ++
              "c372869113adfffc2186c70f87eea2f91b83235ab3113439b5cf1b0fdca9d4db" ++
              "02af34ab48decab4b4b0db27c6fd36f8dad5fae9f395417b3049f8c995318a2e" ++
              "09768869f23a349072fb7c885efb32cd3aee0b35469fd8516ae252e45df0ea25" },
          { digest := .sha384, exponent := "b9bc79", expected := false,
            message :=
              "9570e4ae5307f347703324da8bad990a8659faf8d17acf13ec232d3227ee95e0" ++
              "adef19f6c0ebc07046c62c79853b7ac82bd06a2f9108c07140daea55b562e2f8" ++
              "61d75667f4bd076ddb5b6faa0770a6e5f12286a4db370ef95887049e0eb1de44" ++
              "bb0ee32976e38ee938db33969ab4e40ae038967c376f80523b13c436bc44516c",
            signature :=
              "c442aefba90877c319e5b8b2a87b50778bda701fa2bf5af4724d3eb7f894daea" ++
              "3fd719cbf0fa88ace828a1c7ff1701077efca06b8717fc2953f055d69bf8cac6" ++
              "f5b352da3ea459282903d42e886642c5ecf49dc5c8579f22d88c951a562a335b" ++
              "615df1bffed752abaad6a60612b186a4e971ec2eb8c33d3595a47e8fc871412b" ++
              "8b8f5f2fd262306499dd81f373e29144776c04393a2d433e9e3dd221678b2e62" ++
              "e7f7df1d40238c2c10c6f923c83b055e2a14ede1ec3ec1c48ec95faf0d61831e" ++
              "8539dfa62a3723e57d12bda7f75c2a7bf77d8a4a96ad2ba9a01d615b6ef05bda" ++
              "a85d4e1e4804e316f4d32b8f1c3532366872497f139bea71a4f86ce00edab93e" },
          { digest := .sha384, exponent := "ee7f0f", expected := false,
            message :=
              "33bdcbfd07f82ceb4a4b208a3d3c24316f745360ec1f374ab092df9061303150" ++
              "3d8e825e51d564d1eb68bfc253c72450b6b45de7639449c33a17e7af601bb013" ++
              "38ce2a2d8f13ba9f1728b92a1785cbb960076ca1834dcc274163dd43439daaa3" ++
              "0cc6eaf32b7ad55cb5d1364af23ec27357b6a815b414697eafbcead2717ec809",
            signature :=
              "2077c18cf72a6a6366fa6632a286e116ae694008cfc3f13b1cbc005fee635a31" ++
              "7abea470fdc28fbbe9cefa2f9ed3796488d00a8ef419bae16ac54f5c7c5332f2" ++
              "221b4e753599e20d778d714dc065106d0f023276afbf012c5cfb97ec3a364d27" ++
              "392d2a530acde5b6631b6fe40fb825bf31c7e7dce52e1f9a22fff93f8a5f2a34" ++
              "dfb03fda309c580ba5cd174886ca1af32b24f4733093a4f360c696107943e88e" ++
              "0e9896f78011800e6cda15c94154db4167d4a508e331c08d0127446de659cf2d" ++
              "519f0451a50c38e14572afcaba1e8f0ac218ad250c32cb370b5390e7bb010b6e" ++
              "c10d81c05e86f99c63139bb7190f605fa9ca8c8decacbcfc4d3c6e61d1895c0a" } ] },
    { modulus :=
        "f5596b5c452079319067a1bb3fd2f9c600abe8a8be658285a99b19dfee65f03c" ++
        "52d7e826943a934bb25e79542b7a9e179b6f95698bcc83e19cc6db49bdf71895" ++
        "7206d83621ae4e384eccdf283b52fa3c4e7c0859859b574da49cecdb87249f20" ++
        "f16f0a9d63e6907256d5db57ed3cf12675b0ae63b458a1d4b64a2c508cd6f18a" ++
        "4ec57e5cdf2c62edebf1b739bd01d8a280d3bc88a8a81f9627e4aa83f0656b03" ++
        "ff04710ab4531f4f854a6a9fb326728b8752f61acdcc5e1d8f523e69b32b1ace" ++
        "d6e9850a777048f294365ed98fb85fb4c0a0829279d0346c8efc1ec6afe75761" ++
        "16d15339cdcd1a8fbf4999264bfe22e9b6e5b6dace317c7689b866a72152829b",
      entries :=
        [ { digest := .sha512, exponent := "534f11", expected := false,
            message :=
              "142565e97e8f5f95ec31fa8325beec222b3eedd82062bef364146ae2fe53cca5" ++
              "3d3e51829e6e00faf189b7fbb814b757d089627553aa4447bc14517b4c176df6" ++
              "adc5327ed649edb62e7be950f4b1f17eded710a900c29b66f0c171a62875822c" ++
              "abe38e45ecc82fb3eb2c1aeaa13aa27f9e4f7eddf151cb3a484255c958151231",
            signature :=
              "ec232493d315f0c4ad232653ec9de464c33f956af3718c5b9f1266e7402c61c5" ++
              "ee9c177f14f8dcadd1d074e8f4087516b77b2477e4fdaaf48fd138e89903ff04" ++
              "e11cd0fb07d832ba545025b921496443b52978e215239474a031c44bf96ecb4a" ++
              "ef393fbe0fb52e819cae819af3ab41c48b80afc60aaf41eefcf36cd00c2aea08" ++
              "dd09e5aee0056ed1b7f15ba237daae1cf4fd944dd09596e5dc0f029bf83b5201" ++
              "7018c046e0cb58e3f24593117a624064d5c9afaf9df69bf92c816b72e625bfa5" ++
              "e9cd96e963c62b0cf82eecdc1852c1c02147030fe540dc270e454b4106f8116c" ++
              "bed3231630c7c1345be5f8847f8627fa082675c680a98ff109649fc4399d40aa" },
          { digest := .sha512, exponent := "534f11", expected := false,
            message :=
              "0053b72306191a180e86830fd37a1f13847739cf6ab30149ca6b8ccd0d791d26" ++
              "1e29a315144982fb117f96d969e0757a07bdf5ef0dc0ef3cbb38425192b21a3c" ++
              "b9c9729c9f3fd759e24c6f9270353bd7ec21999953290ddedfae40392bef49fa" ++
              "99da2ca2f123a09a4a9416242ea4f691f94a2cb58213e398fd73906e205833c9",
            signature :=
              "6f17ef5b663a05ad79a4fd77515845d7dcf6fe5eb928f4e6567d7d615277ad79" ++
              "63595baf26971c1ee8db870c9e830d5be09732b8911476b09c1493aa1ce8faa2" ++
              "b527349ebfc882eb93acca56f5c0f5682c784c4094ef86aca1bf36acc97b7a9a" ++
              "96aa349c5f8d2034b92b8a8725be2091f7adaf8c3a1ff14a1e900a35bc6f2eee" ++
              "130595411a3c94aff5d7a0f9f9f5a8df9bbd5b28676ebc587c1f1e26000cc8b7" ++
              "89e8c6974cbd49d58c139fa5847a924f14074d340b7bd4f325773f09d82a0da5" ++
              "4da2d7df251951c5950762c9a3a0d2db10693f4aeeb97780367698aca99a42fa" ++
              "47b5f185e4c607cb0dda51aa2d93611e2f5bca343baef36dd6b0bac18cfa6b73" },
          { digest := .sha512, exponent := "534f11", expected := false,
            message :=
              "b286242ed447af64ee029c7f33b5428d440503773f30748ff843be68868d45ea" ++
              "025387a58bc546668d31e9084377208d7bbdc76e9a630d2edf39d535ecf05cdc" ++
              "82cf1cc58ca7f16d5f097b0440b6c37c265721e0c26f5de7bd8d14c941c65d51" ++
              "ba62ad33ded6f8a1ebf319192f5c7481ce3dda75c03aade019a644c98df69070",
            signature :=
              "dfc19a45dd3b67cfa9a47615cb7f5365f28b85d5c11ca965846326849a2002e6" ++
              "4b8f0e377be83641ca5e795f190aa609bc03f94bae4ea25e681959ac85e0ba28" ++
              "f6d298244c8c6f5c18edd868005c375221729dc434ebeb21e5063fcb281761d2" ++
              "b626276dd14b6e70ab53c3909e8df9f70f8a93a1485ab9794e7ce5c424a53032" ++
              "9bde2834b8363e1f857dd9ff8908f4108c305ef2c303018392324fc600617d5c" ++
              "a4d041eea9a77f116ae29766ceb75a1c5f4931674044c5e48c7b214a2bb6f1da" ++
              "81ccd43ca056776da7b1c0702a9f39ba1cbd861251ea25620eee495e6a8cb00b" ++
              "b0a0963b609086ffe552bc8badaa9aa6a06a9710fd96f6047b8b1660a7680b34" },
          { digest := .sha512, exponent := "534f11", expected := true,
            message :=
              "a5374f49877cfd0734fe20ebe12c360d950416748ae3788ad69cb7cc4ac8d6c6" ++
              "9b5ec23fbf84d6b19aa4a4fcdac1f35a200c049660b21a798af938866a8b2de7" ++
              "cd11cea6e5048320eec005b712db65c88ab451dd074f93235060da1e2ca5bd9b" ++
              "8279fde6bfa70a3e787cc9865120953d1d2684b04661eb6e6ff924fd59bf8ecb",
            signature :=
              "2e985464b882f7c6672154a107154add844b4be163ceb8053be6b6fd632cfbc8" ++
              "6d934e5aea7d11878b4df6e24fb0dce099c5b52bfec0897dc57fb03465adc206" ++
              "7a779d011e64ceadfb1e0a7051c5d248094ec8cc239d80c6e70591d617e54f50" ++
              "3158f2b22b93eeebe017897fcc8f44703c815f07a476bda567dafe122bc07363" ++
              "818c83eddb6f777bb9e84f11549f3cbc283b78b3f2277c7a54072c13032a416c" ++
              "6470395472303c84adc17dc6128cd82c6ccd907ccb93adb0990289bc5b2eaf94" ++
              "8c2f421ad0caf2655cd5839c86aa854370550ce033bc05b7638b8edf67bb5ea9" ++
              "97bd904df293b89a0d16535134b66a6fd5551aec3dc09f29fdecbfc6f474de6b" },
          { digest := .sha512, exponent := "534f11", expected := false,
            message :=
              "dbed25e65429b89264ff6928e6ea9424b862a2df1daf870660fe8f4bbbb55b5a" ++
              "7604260f53bc4ee62a650fb3d18b91933e582522f068cbee8bd8f92cc2a097aa" ++
              "79234e052b05021c8a3d9dc4666b0fbed06b93e67f2a33ac73b88ec8d79fd92a" ++
              "2c742430a4abde1cccaf9cc56e33168db6c27292939ec62960c7d888c45a28c2",
            signature :=
              "d5c50cfbf215c17489ba4d29b5e2f84a4ea244ef0dcec72c3a077e12d74d5865" ++
              "74aa9683cdd0546c3581a723ca048415c6252894e40d3bd803138f78c7c493fc" ++
              "679aa1104e2844bf51618c3571789175828cf7d59addabeb8fa2745d08a247d5" ++
              "937600f8bc0dfe2e1ea7abd257b3e1c207a3be3e2fef8344979c4e0dbbbbfcaa" ++
              "908e1c9c6da303e510f0bb455f4b91dc7fee576e358fd5b2aa8f1e6440bc229c" ++
              "004c31e6e61123aef01a0d382852689ac04424007f55b6fa6aa298b9a93b3ece" ++
              "b6e585f69a5714231e60e1db27b2cf94f7ca5f6fc4118c0604ee716f41736c7e" ++
              "fa6c43a3af42b27b585cb9c6356be864e0514e2bae881f4ad5ddb9aad592d7ab" },
          { digest := .sha512, exponent := "8f3795", expected := false,
            message :=
              "562eea18d9654547cb566556964ead28616c18e0920dd7f691883c8bcf1cd6f9" ++
              "0826deafc597d13c24a65fa9dbc2840c7bcbf55af281bd7d543d28a6dbdfe0e5" ++
              "2c0756f7db88635f321930b82e4e5349cbc73ada81a8cdc60f484f52772e853d" ++
              "4a391b98251e43d87c189f2a96da6106d9c9b10748684ffa4a137935adf10f2a",
            signature :=
              "4df68855dfccab1e7a94430bebb9c631770e7bd75538a9017e2df5b35117db59" ++
              "f8c9f620c1fe41bbc5bc65155355a83c1c1da767bf7e6c40ed61464a53009d7d" ++
              "8d1ee31e7e82c4b97c520d74a60e0de0597b977d07ee95fbbd4e5486d7ad61eb" ++
              "e302de0cd634be178a04c8b9498c89b7ee1c674a074e70ae0f93e7e5dda89c16" ++
              "5808a8ab55337a048ddb7eff91a8b5309ed9941ecdf3ddc3b1e235f7cf139b68" ++
              "1b97cfbc584d9c0359b26a8011dccd7d5ff0475d52959d35e30ad66735bfdd06" ++
              "e63749dd775e65d9407375ee9f5f9e73bf77b75fe0a5923fa7fcafac08e10f05" ++
              "63dfedc2aa2abfaff6f73ba293497eb0159cefd63c974553a24cf0602353fd4b" } ] },
    { modulus :=
        "ec660e20d2b5c6d192540b0f7331da6f1df6126a35861ce249bd0b6aac48c182" ++
        "dbfc5b6716892616810e8c39f9d9c7230771a64810bd9b0146b965135c38751c" ++
        "1793945cef1ed8a799340990ae73d542e26701907b707c3e383f428f87ef5af2" ++
        "b276d0f8dddf8bbeee36824c524b4c38195b9ac69024b65fe5bd6d768166199f" ++
        "3659936824addd4ee488c42480090bad1fec768c339fc172d9692f0c9d176388" ++
        "84cef77c763539b5995573963f12a852511c410833ae0d4b9086a92754f47453" ++
        "032858e6b5f5f215ad48122bec89830a4de5ad86cece5677dec6d6e01ad94d42" ++
        "933c4820269c595e52fef3694521060280c7e505d090aed94bf0b0a3c1596593",
      entries :=
        [ { digest := .sha384, exponent := "19aee1", expected := false,
            message :=
              "2d891e111a8812a6448bc2ac2c234a616997a8579335c36d5fe6acfe0b052358" ++
              "fd715d70a7e104d4ad7880e04a9a7535f0fd8c672e0377f6d7472f8061758034" ++
              "8b60c88a424efc31c696eb49096ec7d358fee1663cb9b423a3ec25eb3b9709cf" ++
              "1f7de8c7b57700a7d60d8d5030474823e9c12ebc85fe82dc0afe15a66213c50f",
            signature :=
              "7dce8f644be457f76b46f3537cd3c1965832e89ffa636f7bca10a2505db17e9b" ++
              "abb7c3e5628fc5323d505efade76ed8a9b702b84c22be49c70b8c3e54b4a1f6d" ++
              "af66c2425ebc03fc6ccb600dbf916048e395aed1a5676db004d917c4021f786c" ++
              "fd0ac332e3e0434907848229af099ee468d6324d54f5b2fd051c7449f55460bf" ++
              "519eb9c076852b017220500168e18cd0358cb2c409acf692b4bfe1c75c4d319a" ++
              "45d465f920fb3f92b5c7025c21479c3e9c85bad8a323ca1fa0f112f448aba0bd" ++
              "fe602734f149f619479b39ae5217a01139c271007748fe5a089294a8c3c35074" ++
              "28c6a11d9ea84ed7c7b35a90d07ac3eee713189d47d4681316de68683c1fc94f" },
          { digest := .sha384, exponent := "9885f3", expected := false,
            message :=
              "8e8fa198e16acb264e1d0d9895af5ade743d7586d554bf39469e4e89a9c13eea" ++
              "2d844cfd7d34a0153746ebf49f3db2d595ceeab0c442c4b91d1dca2984fd2b42" ++
              "c8c4538dd9f9bf67356c10bba4195e11254fcec82812679ffdbd217b8dec3f64" ++
              "4898dfd05e84d02432d8a3780c0c059a0d084c56698a4ff5d0c77b042d552357",
            signature :=
              "421b51d49f5d95922894f0e44dfa5928f1589c632e2c0051b1e085c174e928d9" ++
              "8f035b958564b92daf21408e130815c00b35b32578d320b4e604c77088dfa321" ++
              "fd69f6dbffb2bbcfd53d6d8023d9862598ef38f05f0d44dbe72d108aabcae007" ++
              "6d4dd48e4c38115ee7fccfbeca3fdb69ca26f233284d866aba242c932936a0e1" ++
              "f6d01b668204f7cb534164dac3183e08857b4f150ba6a4a38eb98c4ae2aa983c" ++
              "0c5971e62e687cc63fb9eff8148bf01d14011322cbe85a2bba650200ec39f8e3" ++
              "327196d3587e1f167cfaca4abe538f9f420b3ec5ac95c462ea32a700da870756" ++
              "f7fd759befbfed269956abf4d22d0378096bbef743b0feb15b30e2954cdf3ed2" },
          { digest := .sha384, exponent := "19aee1", expected := false,
            message :=
              "92547ecfdc67a3887d5f686c77bf982d84ef4a951131051d8ad628bcd7b289fd" ++
              "27cd5d54ec5b58b226ef1557e5ebb7e8093bd1c14d43838c8415e61222e8aa52" ++
              "fdc6fed05584b03012f796034e652ce1133a7eb866fc496384815d7f6b60457a" ++
              "9ca52aec20c9f52bc9e1b41aba153f4129541b2364469ecb128254a9bc02a29c",
            signature :=
              "a4c509864fb912cccf022eff3b7e2f4b568fb08aafc498cdacc1fbfa3c7c2766" ++
              "45a7d2d838ed703e2dadc205c77e38e0e326a84c3a9dd3a1d6c5aba50c23e692" ++
              "3378ae1e3edd125751ccdc38d80b91569c20dc517ff1963be1d6cc35d2728bd3" ++
              "cdd0d23d341ba91b58ca868d90490a6a5a88bed3a789d46907b9acb725f18784" ++
              "3b57d22b17b3966971deb99030eb72efeb4704a91683ab488160a5b43de32319" ++
              "fcf609cf00485f2a9a5a3a8eef1ff1b9cc646b8645d958bd002bb152327e92f6" ++
              "beb9f4c3c193f4f35de29c6e7a8739761018430e5144dbeb895857bf5a313570" ++
              "f1e94e9ab2522c6c046f0a8190a995bb49be4cb7a3794f89e1a4c8ab295f70c1" },
          { digest := .sha384, exponent := "19aee1", expected := false,
            message :=
              "1a852bf321f978536e0c9638414beb424afbbc711ab742e7d85b01ef3521553f" ++
              "a10a4e7ac080bdf917398fcb0c5e5afa0ded36100f5cceda3a7fb76ce2ab0065" ++
              "ba1c0a754494991c8c452cb416f18ab115509e28ddb2848e9be5e4c344597f4e" ++
              "cb8207eb977e344334f814fa494ca3eecaeb9bbe6e028d8a645631fa4272fb82",
            signature :=
              "ed0c530de2798f47c15dfedde11d93fa134b243aa2d7ce2bba3718fb1a228f1e" ++
              "c7f6908f56f57166fc2f37c86c22b097f2324bbdccff72f6ff7650fbec45b021" ++
              "1a43ba885a6aa807470a93b08828e04300df4916640e4d8671f22d57ce20f1f0" ++
              "bc89b2f01b55e4aa5426ece11bcd05aabbb3d7434536cfa5256de9b99849e01c" ++
              "a9ffbeb770cc00aba63515aeaf92dac5e03a29f9f2746c2274d60f04d4353d76" ++
              "a174a17c25255a4dbddf8ff11987e2867da69049981e8ab9c1a200788308bda3" ++
              "7c4fad9ddf5ea9b62ba42505bf3ae3ca5ab3d36ec5d67d993817caa1b0a7a225" ++
              "f0b3b42aa5734d7232d2d9e3c0b4cad51b26bd5dd2cefc22fa09ca060ff16801" },
          { digest := .sha384, exponent := "19aee1", expected := true,
            message :=
              "3511607cfd2eea7780877d2c585d1d2043881cebc97ee0ec20b1e73b4c1e07df" ++
              "8a22fb41ef901be14d026b48566cd73e04f7bd3c380cac24a1ae6c30df0e3e28" ++
              "e85964d9abd5e4c2f42c8a1090082ccdb1df3154941154086030a645529ed297" ++
              "175ea52a7924ce823eaee26c4d57a33513ea811925b461fe27dd9e63ecf84d93",
            signature :=
              "e91b444f45a604eb9203d83adc877a36894c5fd6d75c521caeee6a8e57904698" ++
              "a887d0c54398bbf82da4c3aaab349bfc706497d991bdb86b9bcebc4c87df1b90" ++
              "1b47ba95fdd0b8ff4b5dc5bd3300d36ec48e895208e41d569b2545fc7f377679" ++
              "7de5a21dd228da7ec09ea154c987812b12cb4c349e6029e61b9e5c1d30389944" ++
              "45f9d4b5151246a6b7012576cf2aa23afc2e259255663cc1977ac1fe8daed2b2" ++
              "b5d1ac1d0b1a7b6e32e50be4d4c3b3d818d7b650f85726f9d4b505e5491468d7" ++
              "f286bebb4d97fd4dc0854e0f18c0cd0455fd54d57968aad620a670e0f4aebca0" ++
              "70247563d69044c3ddabcc735177e91c99953e00b81de45d01eb3dacc09c1083" },
          { digest := .sha384, exponent := "19aee1", expected := false,
            message :=
              "fe627041cc6368abdc8e193d731ea6235fbede7c969b050b1abcd72f1f96ca15" ++
              "70db942c0f94edd91b6f966df75a9a54a950d48e8073b164fa5c3753e4af464d" ++
              "c3f21e21739f22370e77dc80101a40adb8d5359fb1bb511ff1f7e4d0e2603961" ++
              "bf4e180741ac8f2b7c4ff3600386219753f309966f996ea6c735e78c5ed22abb",
            signature :=
              "3711a7daa81e0a5b897d3d371ab282b660307168c968cc3a1e4e947b32ff2f0d" ++
              "5d766535450b5c227f7a054b7f5110df9fdb6a8b8cdea54185d6ac90c9ad5afb" ++
              "b922d6ace388d121ce977ca4d778b83299a85a74cebd71234c04a1c2afefc034" ++
              "e9905023774b280a063a99a9c8d70cad6ba0b0cb943a2887caccfb3c0b436748" ++
              "a9880052a16f35c467e78243c0d175dcd92875f3f421313f69d040e8222c6ced" ++
              "1ff5ae12e352e8f45c759bec21a1a645c64611ec0dc94b69bc9fd52f287e828e" ++
              "eeec41f17afe3b62e7436d2940479a936bc5d82ff212967484550f1f552f301f" ++
              "e1f189088135de6af7f8e3a49ec5db80fd450bb2d9d52a95cc9607cc3cd1ce15" } ] },
    { modulus :=
        "981ff4f5e7569dde9ea2f3630f0463002799dd234a423f6e960c4b55a57ef478" ++
        "e9bd58b94fe4303c5cf3a97d076e3ff845fdef29be7e9ff293acb652e86a5a26" ++
        "0882cb4e7724a44a08ebd11a168fc389588f0cde26847644febd1f7c6c031ca1" ++
        "eae47f9941a4dca32028f1408eb96db40a386bf922a8aed72fa27a937e181f8d" ++
        "cf35c946bd5405897a0f0fbe00f18b66de336abd51ee46b8ffe4cee6667f3de4" ++
        "dec041774fd79a08b0a2be1fa16806c6b58ed795ab9044b732f69a1cf88f61ba" ++
        "862f24462bdb036d5d5701ba205e37c737e8da703e9dff2208051e537939e1f2" ++
        "643efa2261f268ee31021379681cfad9a1c03d91a6f17a316cca2e810a0ffcc3",
      entries :=
        [ { digest := .sha512, exponent := "08475b", expected := true,
            message :=
              "7120a0657a833d7f9723b647eb6867f5d9f6f1fb1a77e8eb0c9acc954d5b3b6f" ++
              "8986643b9076bfe3ac23fca8315c397b555077ab42534fc16adfe1a91bd90e12" ++
              "5316e716d51e641e7c305a00d086a76bd7d9af852e280dd257b6825855523101" ++
              "76da0f40710295f7b052b899ef6e1a8c069a82d1037d8ae67c2597eb244c0e05",
            signature :=
              "385f2fe2bb8e9483bbc05c316283ad01f8aea41bd83ad941fec99bad0f066fb1" ++
              "c7dc960d536d4ed5302958a0df7b943836878a1c906b3f3f778e7335407676c7" ++
              "766183ef61624c32da8e79640ad5390660a46610b2b172dfb7fdf48e556408e0" ++
              "da06ddeab4468a00abf93d6e3fd71c04478b49f394e849f1923d4a57b76f6407" ++
              "675fe647f7bcc59f7493128e62c0cbf999dd4b3c62cbba2accfbf77351abf769" ++
              "27b89cb6f57d900d631d2445231f75b7d2c3ef303a51b38f9e7f0d69a68ab397" ++
              "674628a825ae74605f32deab2a0ec2fde1fe820b48d824b68acef3f0bdbd7804" ++
              "eb15899029bc9d349951d732eceeb3c42ed02ab35d112841f8e411b28435ddbb" },
          { digest := .sha512, exponent := "fd8739", expected := false,
            message :=
              "77449a132998a90b149b91bd05fb1e53c85e28d7923e16a69cf7a122111edba8" ++
              "2a156fc297dc2a9d222ababd8fbdb6efc6eedf7f3488a6ac6edaee59170b1205" ++
              "05ae2afd9f968ad089ec8c04847e90078f5a4068529c1947bd84270bedcc0f53" ++
              "4f38532e076ed28e93088efaabe8b2846ccbd4fbb6217761d31dd49f5908da78",
            signature :=
              "240add12876bc54e013030c890f3abf774a109f687effbbb6a03d0b828e8e1ad" ++
              "a27e424db835c78dc0d6905b212fbfd55885417d571e7da1cb1566a1cb713cb0" ++
              "4a334eaa68545cb17cfe55c037230a5a71e941fe51517530392ed35b844ab7e8" ++
              "91e9230d67250c7fe73a9d969523815dcbdae4c01322648cb0c686aebba24c4e" ++
              "57cc4859fd0e38a23dd43f86373d7c3250bd03d8400887926df0f98169c132f8" ++
              "19180b9fc482ec77304b8af96a5334401912e6d210361218267c21f2c65d3a83" ++
              "c376516b869466278841e267d73237789b33e5a7ac3f1feb2a1a3e9bae60523e" ++
              "d5f814124805f11c151357fbb8a717fb8c858c66e647ddcb59c20c2bb8e86abc" },
          { digest := .sha512, exponent := "08475b", expected := false,
            message :=
              "f99ed2fc9e07ccafe0704660b1906e93542e3c7220d8551c81d8303f3f6477e9" ++
              "0315b09b179b1ca06daedf9ce3476268c511f61d931aba6f05cfbe3d4d276865" ++
              "9c1e17dde7650700eb5875256f300376c97a5d00a3c81d06ffa6ec9b79cfea70" ++
              "cca151ea98cf557763564e23ddb218666851ba40d7484788764502824bc4c5af",
            signature :=
              "268ffe2eef8407c215d1e0d02d3b23d387900877d4b6ab515a9d35e30d6c6483" ++
              "0e748ab782191f2f9a9c133765ec3863708dbdd36d5e4ce9dd262f040766829e" ++
              "365ccf8e19b146355770ec4dc3a059581efe466e59fdf1d6a7d0c6a24b052c54" ++
              "b5a0f02e73390cd70ac56c0a004a9e45ae81296b3f5f1677db8c0dbae012295e" ++
              "b884130530215c175239e7160182009b46607a71a6186c48a1b8cb45c1dce3fd" ++
              "2f31aba568065e8e490f021454a674b8dda3e436b375f0daa3294969492ed269" ++
              "e9156011b133de86ada6a84225b1c297b71b3462cd3ca037585bb805179d7686" ++
              "4a9083f927e8e1360d9302a2be39166bd5411c997000d882b268623bdc5dc9d9" },
          { digest := .sha512, exponent := "08475b", expected := false,
            message :=
              "019d049056b4bbaf6c585c6aa4b7670ea52fd6814e6dad83eed6d334b82520d6" ++
              "7156b7d56cc49604b88e6b2a983ea9bd33addced8d213ae5b6b97a4d420be913" ++
              "f80bba6bcf2f9d1416d094ddf2d402690d8a052f8dd506c4438d8f5d25225c90" ++
              "ff82b45a653dfa66ece77f8c9abf9a999a8dfb4e34d13cabfd19b96d4bb3a2d5",
            signature :=
              "772e888d14c70c4e546fa77a85d1be25ef85bd24ea52db68c2c0d3889edf96a6" ++
              "d7d31696536a12fead53f44a055847be51567a6466730991383e5aee41da40c9" ++
              "0d6c951e36c865fa4638490ab44a27cbaedaad7d415b80a51ab465c8a18df567" ++
              "356988020d7e6ec0404577ce8f02d581e48228bc342f6bfe2d2eb2dec17f66fa" ++
              "e7debb40b839b1085c16caa417bf31a7bfa540405f76671c8d80dee48d8a1cd4" ++
              "4b456ee61ba601938bb3626805c232ec3978936bd8dcea073ea483ba8cdc2984" ++
              "1b442fd28b4b4b1a282298776d83b2174114766b2017e5ad547a1021fcc3b829" ++
              "ba30f0cbdcfbae09c5e0101f8ebf1fdbfa1e1d029bba61c1ca1920fb36ea6e2f" },
          { digest := .sha512, exponent := "08475b", expected := false,
            message :=
              "1c0c43b58a3c85bc56763bb26f8060b645988d11d0651bc6d32e886b624a1b38" ++
              "a2d8cb5ed0b05e998499ce0937bcf03e03585792abb877bbdb6206a0b192a86c" ++
              "7be6cae1c35bcef089786986cfc94aa85b8ffdc2b8b60e3c7e07714fd39f2117" ++
              "32a008e96b261fe6eb7dd6d03e91b61dd2a5454afe482a724285911fd15bd160",
            signature :=
              "5be423f5b70087c95d748e060004afca6b49fea89dfb37c2460578af2484c0b9" ++
              "ac384193dd47bd06736c071b557aad22684016e6d97e9597f49d11edd8bc7e6d" ++
              "c44ed1f94403d171b215b00c8f3a6721e1cd4d37cebf67b705dee052a2cc9741" ++
              "5fa9fac97180fd60ae20667af437d3caf6b69ac87eb9afc3c951a49719f32a9e" ++
              "12062500b958a5b48136bb41e4d6434d5fb59814384e06a4e4d0a779f044e873" ++
              "d5ceea1249f9648153663234cfe9171f988e12926059c896793bb56630432c5d" ++
              "3305d70b436f041c3eb1b6377cf01b27f507a9a8389f57b2b17010b808123ef2" ++
              "3201da72f39febf7ea3841cdbe376d3ac89471f2494e948702f618ce382fde3d" },
          { digest := .sha512, exponent := "08475b", expected := false,
            message :=
              "21ea231df11ec8a62b2bb1fb3a19d608e3ed32a531cf62d4b26c6e43e39ae719" ++
              "e83a32ef8063231b39bdce35e02a99d43cac9699fc83106fed956410701312cc" ++
              "2c5a148600176fff3baf075710deb7d0449ea1d62a4ac33cd103ccc97c532df3" ++
              "521072ea5783d3d89bca0667b27b5885638afc64a46da3c4c77d4d74eea05e16",
            signature :=
              "0020d90f8361337e7196010e8778794c721c881492e63ceac4a7bbf56daa41fb" ++
              "b9c1716be12b56b79fc826b090c3a2a73f85fe761c9249f0be8577ca78385d11" ++
              "ece10270c05d07590b8d3c889f4cf9cc0881c066957974804f4a74aa9eed9a7d" ++
              "26871885260b2d67c96b1cdac2a6ea61650d8324dfc37105b916ecc406d604f7" ++
              "9bbd7c8a7754cf805cc9c74914dfa1bd2dd6ab62b0e228673ac84faeb9b38c94" ++
              "f3f1a1b74d83188837dc7cdf8521bb61c7378c3db6c2305bfa906ab1c6ba3c2f" ++
              "e557feaa5c97e28304a64f3b4153265cf51910a7636b3723cd56131ea16ab4ad" ++
              "865224088143d36f7fe25c9f18363953b33692c10fa3aed59eb70172d7f4708b" } ] } ]

public def checks : List (String × Bool) :=
  let flattened := groups.flatMap fun group => group.entries.map fun entry => (group.modulus, entry)
  flattened.mapIdx fun index (modulus, entry) =>
    (s!"CAVP SigVer15 2048/{digestName entry.digest} case {index}, Result = {resultName entry.expected}",
      Rsa.verifyPkcs1v15 entry.digest
        { modulus := natOfHex modulus, exponent := natOfHex entry.exponent }
        (bytesOfHex entry.message) (bytesOfHex entry.signature) == entry.expected)

end Tests.Pkcs1Cavp
