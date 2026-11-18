module

public import ArmillaryLean.Instances.MinNumeric8749
public import ArmillaryLean.Instances.WordData8749.X

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion

namespace MinX20

def part4Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x2400014b26213637636a005001d3400226213637636a152005001c0c00213926213637636a005001ada00213637636a2871400050019a1002875002d10002)
        (.chunk 42 0xbe600223d00037636a37812a118005001e2600237636a37512a112005001cfb00226237636a38412a005001a9f00237636a36912a12d00500184d002ab2002))
      (.append
        (.chunk 42 0x262386376123004001aa0002111000238259262003001e21002226259262003001bc700226237422d003001a8e002259262350003001962002cf900284c002)
        (.chunk 42 0x23312e005001ced00237625926210212e005001bb800237625926210912e005001a8300223f00025926237a376004001e25002259262261376004001ab1002)))
    (.append
      (.append
        (.chunk 42 0x36a376262279005001ac900236a37626226f00c00500198900238200236a376262005001864002d0e00236a00037625926210812e005001e18002259262105)
        (.chunk 42 0x263012006001ac800224136a37636e26300d00600198700236a37638336e26301500600186600285100226300025700025f00236a376129005001be2002014))
      (.append
        (.chunk 42 0x6001ac800226824436a37626300d00600198700224436a376383263015006001866002ab600225600036a37612b26036e263006001be300224136a37636e)
        (.append
          (.chunk 42 0xac800226536a37625d26300d00600198700236a37638325d263015006001866002be800225600024436a37612b260263006001be300226824436a376263012)
          (.chunk 22 0x25600036a37612b26025d263006001be300227a26536a376263012006001)))))

theorem part4Ok : Numeric.run WordsX.word 909 3636 10
    [2429, 2136, 1820] 0x200000000000000000000000000000000000000000000000000000000000000000000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part4Data = true := by
  decide +kernel

theorem part4 : Excluded (numericRows 0) 10
    ([2429, 2136, 1820] : List Nat).toFinset (checkpointSet 6 2 [2429, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part4Ok

def part364Data : Program :=
  (.append
    (.append
      (.chunk 42 0x36a37625627c03101c006001d2a00236a376256279031016006001bff00236a37625629603102e006001ae500200836a3762562880310060019a3002880002)
      (.chunk 42 0x376256261001006001d0f00200836a37625625e12a006001be400200836a37625627b013006001aca00200836a376256381016006001865002988002141000))
    (.append
      (.chunk 42 0xa010006001d1e00236a37625628a00a022006001ad900200836a37625627c00a00600199700236a37625626100a025006001874002bf300225500000836a)
      (.append
        (.chunk 42 0x6001bf000200836a37628700d01f006001ad600201a00836a37627900d00600199400200836a37625e00d022006001871002d1b00213500036a376256270)
        (.chunk 10 0x26d00013200000836a37626a00d007))))

theorem part364Ok : Numeric.run WordsX.word 909 3636 10
    [2749, 2136, 1820] 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part364Data = true := by
  decide +kernel

theorem part364 : Excluded (numericRows 0) 10
    ([2749, 2136, 1820] : List Nat).toFinset (checkpointSet 6 2 [2749, 2429, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part364Ok

def part542Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x36a37600d00500198700238236a376383015005001866002cdf00238236a3762560f4207006001bab00238236a3762560f9215006001a7600296e002bd6002)
        (.append
          (.chunk 42 0xfb38236a376256221006001e070022560000f838236a376000005001d1000238236a37612b260005001be30020f838236a376012005001ac80020f8382)
          (.chunk 42 0x36a376256374380006001e1f00238236a37625638010b006001cf300238236a37625638a380006001aab00212838236a376256380006001975002a9a00235c)))
      (.append
        (.chunk 42 0x37612b260006001be300238523238236a376012006001ac800238523238236a37600d00600198700223238236a376383015006001866002bd3002239000382)
        (.append
          (.chunk 42 0x12006001ac800237f24438236a37600d00600198700224438236a376383015006001866002e2d00225600038523238236a376000006001d1000223238236a)
          (.chunk 42 0x36a37625627b134006001995002869002e3100211d00025600026237f38236a376000006001d1000224438236a37612b260006001be300237f24438236a376))))
    (.append
      (.append
        (.chunk 42 0x36200500197400284c002aa000201800013f25912536a376256006001d2800225912536a376256146006001c0000225c25912536a376256006001ace002125)
        (.append
          (.chunk 42 0x109111123005001a83002cf900212300038512512e376256005001e3300212512e376256251005001bdc00223812512e376256005001aaa00212512e376256)
          (.chunk 42 0x212525626137612336a006001ab100236a000125256108123111005001e18002256105233123111005001ced002125256102123111005001bb8002125256)))
      (.append
        (.chunk 42 0x36a25636911e106006001cef00212537636a25637811e006001a9300237636a25635d11e121006001970002bd500223f00012525637a37612336a006001e25)
        (.append
          (.chunk 42 0x37636a012006001ac800212224d12537636a00d00600198700224d12537636a383015006001866002bda00223100037636a25636c11e10c006001e1a002376)
          (.chunk 29 0x24b00038600025600012224d12537636a000006001d1000224d12537636a12b260006001be300212224d125)))))

theorem part542Ok : Numeric.run WordsX.word 909 3636 10
    [2136, 1820] 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part542Data = true := by
  decide +kernel

theorem part542 : Excluded (numericRows 0) 10
    ([2136, 1820] : List Nat).toFinset (checkpointSet 6 2 [2749, 2429, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part542Ok

theorem part362 : Excluded (numericRows 0) 10
    ([2136, 1820] : List Nat).toFinset (checkpointSet 6 2 [2429, 2136, 1820]) := by
  apply split_excluded 2749
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part364
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part542

theorem part2 : Excluded (numericRows 0) 10
    ([2136, 1820] : List Nat).toFinset (checkpointSet 6 2 [2136, 1820]) := by
  apply split_excluded 2429
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part4
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part362

def part1037Data : Program :=
  (.append
    (.append
      (.chunk 42 0x27436a25611e24326a006001e2c00227436a25611b24626a006001d0400225c27436a25622d26a006001bce00227425c36a25626a237006001a9900298d002)
      (.chunk 42 0x24325526a27b006001e2c00225611b24625526a27b006001d0400236a25622d25526a27b006001bce00236a25627b25526a237006001a99002aca00237e000))
    (.append
      (.chunk 42 0x26a276006001e2c00236a25611b24626a276006001d0400211936a25622d26a276006001bce00211f36a25627626a237006001a99002bfc00237e00025611e)
      (.append
        (.chunk 42 0x6001e2c00225611b24613826a273006001d0400236a25622d13826a273006001bce00236a25627313826a237006001a99002d2100237e00036a25611e243)
        (.chunk 10 0x1300037e00025611e24313826a273))))

theorem part1037Ok : Numeric.run WordsX.word 909 3636 10
    [2146, 2437, 1820] 0x20000000000000000000000000000000000000000000000000000000000000000000000004010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1037Data = true := by
  decide +kernel

theorem part1037 : Excluded (numericRows 0) 10
    ([2146, 2437, 1820] : List Nat).toFinset (checkpointSet 6 2 [2146, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1037Ok

def part1217Data : Program :=
  (.append
    (.append
      (.chunk 42 0x36a25613d24f26a37b006001d2300213f36a25624f26a37b006001bfb00236a01513124f26a37b00600199200236a25603937b24f26a00600188a00285f002)
      (.chunk 42 0x36a25613d26a006001d2300213f25927136a25626a006001bfb00225925613126a27136a00600199200225914b36a25603926a00600188a00298a002278000))
    (.append
      (.chunk 42 0x26a273006001d2300213f36a25613b26a273006001bfb00236a01513113b26a27300600199200236a25603927313b26a00600188a002bf9002278000259271)
      (.append
        (.chunk 42 0x6001d2300213f36a25613526a270006001bfb00236a01513113526a27000600199200236a25603927013526a00600188a002d1e00227800036a25613d13b)
        (.chunk 10 0x1000027800036a25613d13526a270))))

theorem part1217Ok : Numeric.run WordsX.word 909 3636 10
    [2759, 2437, 1820] 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000004010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1217Data = true := by
  decide +kernel

theorem part1217 : Excluded (numericRows 0) 10
    ([2759, 2437, 1820] : List Nat).toFinset (checkpointSet 6 2 [2759, 2146, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1217Ok

def part1395Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x24f23726a363006001d0900236a25623923726a363006001aab00236a25624323726a363006001aa500236a25601f36323712f00600186e002976002be1002)
        (.append
          (.chunk 42 0x24f26a006001d0900224138836a25623926a006001aab00224138836a25624326a006001aa500238824136a25601f12f00600186e002aa100238a00025612a)
          (.chunk 42 0x26a005001bed00201c23a01f26026a005001ad300227623a01f26026a00500199100236a26023a01f00a005001d1800286e002aaf00238a00038836a25612a)))
      (.append
        (.chunk 42 0x26a23a11e37e004001e2c00237b26a23a118004001d0100226926a23a001004001ab800236f26a23a004004001853002be3002aa500212f00000423a01f260)
        (.append
          (.chunk 42 0x212536a23926026a23a006001aab00226000025612b26a23a243005001d0b00225612b26a23a24300500197a00225612b26a23a243005001872002243000)
          (.chunk 42 0x238a00023a00011526026a24f12a005001e2300210f26026a24f12a005001cf800238126026a24f12a005001a9c00236a36626026a24f00500184a002d09))))
    (.append
      (.append
        (.chunk 42 0x36a25612a24c26a387006001d0900236a25623924c26a387006001aab00236a25624324c26a387006001aa500236a25601f38724c12f00600186e002d06)
        (.append
          (.chunk 42 0x369006001be400236a25623c23d26a369006001aae00236a25624623d26a36900600197900236a25602236923d13200600187100284d002d0c00212700038a)
          (.chunk 42 0x1be400224725f36a25623c26a006001aae00224725f36a25624626a00600197900225f24736a25602213200600187100297800225e00036a25625523d26a)))
      (.append
        (.chunk 42 0x236a25623c24026a266006001aae00236a25624624026a26600600197900236a256022266240132006001871002ab500225e00025f36a25612a25526a006)
        (.append
          (.chunk 42 0x25623c25826a261006001aae00236a25624625826a26100600197900236a256022261258132006001871002be700225e00025612a25524026a266006001be4)
          (.chunk 17 0x25200012d00025e00036a25612a25826a261006001be400236a)))))

theorem part1395Ok : Numeric.run WordsX.word 909 3636 10
    [2437, 1820] 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000004010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1395Data = true := by
  decide +kernel

theorem part1395 : Excluded (numericRows 0) 10
    ([2437, 1820] : List Nat).toFinset (checkpointSet 6 2 [2759, 2146, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1395Ok

theorem part1215 : Excluded (numericRows 0) 10
    ([2437, 1820] : List Nat).toFinset (checkpointSet 6 2 [2146, 2437, 2136, 1820]) := by
  apply split_excluded 2759
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1217
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1395

theorem part1035 : Excluded (numericRows 0) 10
    ([2437, 1820] : List Nat).toFinset (checkpointSet 6 2 [2437, 2136, 1820]) := by
  apply split_excluded 2146
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1037
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1215

def part1878Data : Program :=
  (.append
    (.append
      (.chunk 42 0xe36a25627f03401f006001d2d00200e36a25627c034019006001c0200200e36a256299034031006001ae800202c00e36a25628b0340060019a6002883002)
      (.chunk 42 0x36a256264004006001d1200237900e36a25626112d006001be700237900e36a25627e016006001acd00237900e36a25638401900600186800298b002144000))
    (.append
      (.chunk 42 0x5001862002d2100237900e36a28d00d025006001adc00202037900e36a27f00d00600199a00237900e36a26400d028006001877002bf600225800037900e)
      (.append
        (.chunk 42 0x6001874002d1e00213800001300036a27613e00d273005001bfc00236a27b25500d273005001aca00225c37936a00d27300500198d00236a37e00d273252)
        (.chunk 40 0x27000013500037936a25626d01000a006001bf300200e36a25628a010022006001ad900237900e36a25627c01000600199700200e36a256261010025))))

theorem part1878Ok : Numeric.run WordsX.word 909 3636 10
    [2139, 2752, 1820] 0x100000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000090000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1878Data = true := by
  decide +kernel

theorem part1878 : Excluded (numericRows 0) 10
    ([2139, 2752, 1820] : List Nat).toFinset (checkpointSet 6 2 [2139, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1878Ok

def part2088Data : Program :=
  (.append
    (.append
      (.chunk 42 0x25627f03426600301f006001d2d00225627c034266003019006001c02002256299034266003031006001ae800236a25628b0342660030060019a6002883002)
      (.chunk 42 0x25625a258003006001d1100200201136a256258003006001be900201136a256240258003006001ab500213936a25602725800300600187800298b002144000))
    (.append
      (.chunk 42 0x300d006001d1100200225c36a13800300d006001be900236a12d24013800300d006001ab500213936a02700d138003006001878002bf600226600001136a)
      (.append
        (.chunk 42 0x6001d1100225c36a256135003010006001be900225612d240135003010006001ab500236a256027010135003006001878002d1e00226600000536a25a138)
        (.chunk 10 0x27000026600036a25625a135003010))))

theorem part2088Ok : Numeric.run WordsX.word 909 3636 10
    [2432, 2752, 1820] 0x100000000000000000000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000000000000000090000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2088Data = true := by
  decide +kernel

theorem part2088 : Excluded (numericRows 0) 10
    ([2432, 2752, 1820] : List Nat).toFinset (checkpointSet 6 2 [2432, 2139, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2088Ok

def part2266Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x20a13800d005001bae00236a0fc00d138218005001a79002bf600201138536a25625835f00600198b00238536a25603435f144006001883002971002bd9002)
        (.chunk 42 0x23c144006001883002a9d00227000038536a25601013535f006001d1e00235f00038536a22413800d005001e0a00222638536a13800d005001ce200236a0f7))
      (.append
        (.chunk 42 0x6001883002aa700227000038536a01013523c383006001d1e00238536a00d13823c383006001bf600201138536a25823c38300600198b00238536a034383)
        (.append
          (.chunk 42 0x883002e3000227000038838536a256010135006001d1e00223538838536a00d138006001bf600223538838536a25625800600198b00223538536a256034144)
          (.chunk 42 0x12000027000038238536a256010135006001d1e00224738238536a00d138006001bf600224738238536a25625800600198b00224738536a256034144006001))))
    (.append
      (.append
        (.chunk 42 0x27f03438901f006001d2d00236a25627c034389019006001c0200236a256299034389031006001ae800212836a25628b0343890060019a6002883002d05002)
        (.chunk 42 0x256258006001bdd00212836a256121234258006001aa900212836a256126242258006001aa300225c12836a25601b25800600186c00298b00214400036a256))
      (.append
        (.chunk 42 0x6001bdd00212836a12123413800d006001aa900212836a12624213800d006001aa300225c12836a01b00d13800600186c002bf600238900025001112836a)
        (.append
          (.chunk 42 0xbdd00236a256121234135010006001aa900236a256126242135010006001aa300212836a25601b01013500600186c002d1e00238900012525012836a13800d)
          (.chunk 14 0x24e00027000038900025012836a256135010006001)))))

theorem part2266Ok : Numeric.run WordsX.word 909 3636 10
    [2752, 1820] 0x100000000000000000000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000000000000000090000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2266Data = true := by
  decide +kernel

theorem part2266 : Excluded (numericRows 0) 10
    ([2752, 1820] : List Nat).toFinset (checkpointSet 6 2 [2432, 2139, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2266Ok

theorem part2086 : Excluded (numericRows 0) 10
    ([2752, 1820] : List Nat).toFinset (checkpointSet 6 2 [2139, 2752, 2437, 2136, 1820]) := by
  apply split_excluded 2432
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2088
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2266

theorem part1876 : Excluded (numericRows 0) 10
    ([2752, 1820] : List Nat).toFinset (checkpointSet 6 2 [2752, 2437, 2136, 1820]) := by
  apply split_excluded 2139
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1878
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2086

def part2662Data : Program :=
  (.append
    (.append
      (.chunk 42 0x14213636a256287293006001d3200214213636a25629301e006001c0600214213636a25629d293006001aed00203b14213636a2562930060018880029ad002)
      (.append
        (.chunk 42 0x13636a12b260006001be300229814514213636a012006001ac800229814514213636a00d00600198700214514213636a383015006001866002ae600214c000)
        (.chunk 42 0x36a012005001ac800204d14213636a00d00500198700214213636a38301500500186600289a002c1800225600029814514213636a000006001d10002145142)))
    (.append
      (.chunk 42 0x14213636a2562af006001aff00214213636a2562a50420060019bf00225600004d14213636a000005001d1000214213636a12b260005001be300204d142136)
      (.append
        (.chunk 42 0x13636a012006001ac800229215714213636a00d00600198700215714213636a383015006001866002d4000215e00003814213636a256299006001d4400204a)
        (.chunk 27 0x3000025600029215714213636a000006001d1000215714213636a12b260006001be3002292157142))))

theorem part2662Ok : Numeric.run WordsX.word 909 3636 10
    [2177, 3058, 1820] 0x4000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2662Data = true := by
  decide +kernel

theorem part2662 : Excluded (numericRows 0) 10
    ([2177, 3058, 1820] : List Nat).toFinset (checkpointSet 6 2 [2177, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2662Ok

def part2901Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x1713636a00d005001987002d1c00238201713636a25613a006001bf400225038201713636a256006001ac200238201713636a25637a00600185d002864002)
        (.chunk 42 0x200c00025600013636a13326e000005001d1000201713636a26026e005001be300213636a13326e012005001ac800236a13338326e015005001866002382))
      (.append
        (.chunk 42 0x225636a27113213a00500199400213636a03d13a14d00500188c002bf400225001425613636a279006001ac200201425613636a37a27900600185d002ac9)
        (.chunk 42 0x13636a25f36800c00600184b002be200200c00013301425613636a279006001d1c00227900036a27101913e13a005001d2700236a27101614113a005001bff)))
    (.append
      (.append
        (.chunk 42 0x2400500187500285d002d0e00212900038b25613636a25f00c006001d0a00223e25613636a25f00c006001ab000213636a25f38c24500c006001aa6002256)
        (.chunk 42 0x25025636a002263006001ac200226300025636a00213637a005001be600200212a23d13637a005001ab200200200013637a24b00500197d00225636a00237a))
      (.append
        (.chunk 42 0xbe600236a00212a23d136005001ab200236a00200013624b00500197d00213325636a002024005001875002d1c00227125636a00213a263006001bf4002274)
        (.chunk 13 0x25700000c00026300025613336a002136005001))))

theorem part2901Ok : Numeric.run WordsX.word 909 3636 10
    [2441, 3058, 1820] 0x4000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000200000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2901Data = true := by
  decide +kernel

theorem part2901 : Excluded (numericRows 0) 10
    ([2441, 3058, 1820] : List Nat).toFinset (checkpointSet 6 2 [2441, 2177, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2901Ok

def part3208Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x13612f37526a006001d1800236a13626d135007375006001bf300236a13627224c007375006001ac100225325636a136007375006001984002859002abe002)
        (.chunk 42 0x25b261006001d1500225636a13613226126a006001bf000225000225636a13626100600198100225636a13637224626100600185600297c00200a00025636a))
      (.append
        (.chunk 42 0x6001d1500236a13613211e38126a006001bf000225025636a13611e38100600198100225636a13637211e381006001856002bd800200700025636a136267)
        (.chunk 42 0xbde00236a13638c237007384006001aac00223e25636a136007384006001a9e00236a136360234007384006001973002e3200200700036a13626725b11e381)))
    (.append
      (.append
        (.chunk 42 0x36a01c00600199600200e02325636a26302400600187500225f00e02325636a01a00600172b002870002d1a00224900012400036a13638724f007384006001)
        (.chunk 42 0x6001ace00200e25636a13638627b00600186900299500213600025f00e02325636a00f006001d1f00225f00e02325636a021006001ad700225f00e023256))
      (.append
        (.chunk 42 0x9a000202025636a136049159006001898002ad500201800013f00e25636a13627b006001d2800200e25636a13614627b006001c0000225c00e25636a13627b)
        (.append
          (.chunk 42 0xe26b25636a136374006001857002bee00228500002025636a13602514a006001d3300202025636a13602214d006001c0b00200e02025636a13613e006001)
          (.chunk 36 0x26f00013400000600025c00e26b25636a136006001d1600224a00e26b25636a136006001abc00226b25636a136269251006001983002)))))

theorem part3208Ok : Numeric.run WordsX.word 909 3636 10
    [3058, 1820] 0x4000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000200000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part3208Data = true := by
  decide +kernel

theorem part3208 : Excluded (numericRows 0) 10
    ([3058, 1820] : List Nat).toFinset (checkpointSet 6 2 [2441, 2177, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part3208Ok

theorem part2899 : Excluded (numericRows 0) 10
    ([3058, 1820] : List Nat).toFinset (checkpointSet 6 2 [2177, 3058, 2752, 2437, 2136, 1820]) := by
  apply split_excluded 2441
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2901
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3208

theorem part2660 : Excluded (numericRows 0) 10
    ([3058, 1820] : List Nat).toFinset (checkpointSet 6 2 [3058, 2752, 2437, 2136, 1820]) := by
  apply split_excluded 2177
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2662
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2899

def part3584Data : Program :=
  (.append
    (.append
      (.chunk 42 0x15438b13f02036a256006001d3d00238b13f02036a25615b006001c1500214238b13f02036a256006001ae300213f02036a2562901490060019aa00287e002)
      (.append
        (.chunk 42 0x13002036a256126005001d1900202036a256137126005001bf100227102036a256126005001abf00202036a25637712600500185a002bdf00298600202d000)
        (.chunk 42 0x24d02036a38b260005001abf00202036a37738b26000500185a002d0b00202036a25627638b009006001ac600201402036a25638b009006001861002009000)))
    (.append
      (.chunk 42 0x36a25625e00400600197900202036a256372004007006001856002abb00225400000900013002036a38b260005001d1900202036a13738b260005001bf1002)
      (.append
        (.chunk 42 0x36a00d00600198700213338b02036a383015006001866002bef00224600002036a256381004121006001e2f00202036a25637e00411b006001d0400238b020)
        (.chunk 38 0x26c00025600000813338b02036a000006001d1000200838b02036a12b260006001be300200813338b02036a012006001ac800200813338b020))))

theorem part3584Ok : Numeric.run WordsX.word 909 3636 10
    [2157, 3351, 1820] 0x80000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000002000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part3584Data = true := by
  decide +kernel

theorem part3584 : Excluded (numericRows 0) 10
    ([2157, 3351, 1820] : List Nat).toFinset (checkpointSet 6 2 [2157, 3351, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part3584Ok

def part3834Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x88a00238300001436a24802d004001e2e00224a01436a02d004001bd700236a11b22e02d004001bd200236a12002d23c004001a9d002bfb00286600287e002)
        (.chunk 42 0x19aa002bfd00227d25936a27825602d006001acb00227800036a13d13f38302d005001d2300201013f38302d252005001ac700236a03913f38302d005001))
      (.append
        (.chunk 42 0x27825602d006001d2500202d00015436a143278256005001d3d00236a15b143278256005001c1500214236a143278256005001ae3002290149143278256005)
        (.chunk 42 0x254383005001d1900236a137278254383005001bf100224d36a278254383005001abf00236a37727825438300500185a00286600298600201500027713c36a)))
    (.append
      (.append
        (.chunk 42 0x2866002abb00201500013c36a009278254256006001d2500236a143009278254256006001bfd00225936a009278254256006001acb00200900013036a278)
        (.chunk 42 0x246006001acb002246000381383278004121005001e2f00236a37e27800411b005001d0400212e25e383278004005001979002372383278004007005001856))
      (.append
        (.chunk 42 0xac700200836a13303938300500188a002866002bef00201500013c36a256278004246006001d2500236a143256278004246006001bfd00225936a256278004)
        (.append
          (.chunk 42 0x256006001bfd00225900836a133278256006001acb00227800000836a13313d383005001d2300200836a13313f383005001bfb00236a133010383252005001)
          (.chunk 19 0x26c00001500013c00836a133278256006001d2500200836a133143278)))))

theorem part3834Ok : Numeric.run WordsX.word 909 3636 10
    [2450, 3351, 1820] 0x80000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040020000000000000000000000000000000000000000000000000000000000000000000002000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part3834Data = true := by
  decide +kernel

theorem part3834 : Excluded (numericRows 0) 10
    ([2450, 3351, 1820] : List Nat).toFinset (checkpointSet 6 2 [2450, 2157, 3351, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part3834Ok

def part4189Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x1d02214702d006001d3000213f36a01d01f14a02d006001c0800225613f36a01d13b02d00600199d00213f36a01d04602d15600600189500287e002ad2002)
        (.chunk 42 0x254009006001d3000236a01d01f14a254009006001c0800225636a01d13b25400900600199d00236a01d04600925415600600189500298600228200013f36a))
      (.append
        (.chunk 42 0x6001d3000236a01d01f14a246004006001c0800225636a01d13b24600400600199d00236a01d046004246156006001895002abb00228200036a01d022147)
        (.chunk 42 0xd3000225600836a01d01f14a006001c0800213325600836a01d13b00600199d00213325636a01d046156006001895002bef00228200036a01d022147246004)))
    (.append
      (.append
        (.chunk 42 0x13f02d006001ab900225636a13f26602d24e00600198000226825636a13f37102d00600185400287e002beb00226c00028200025600836a01d022147006001)
        (.chunk 42 0x6001ab900236a26826625400924e00600198000225636a26837125400900600185400298600200300025926825636a13f02d006001d1300224726825636a))
      (.append
        (.chunk 42 0xab900236a26826624600424e00600198000225636a268371246004006001854002abb00200300025925636a268254009006001d1300224725636a268254009)
        (.append
          (.chunk 42 0x25600836a26826624e00600198000213325600836a268371006001854002bef00200300025925636a268246004006001d1300224725636a268246004006001)
          (.chunk 26 0x13100026c00000300025913325600836a268006001d1300224713325600836a268006001ab9002)))))

theorem part4189Ok : Numeric.run WordsX.word 909 3636 10
    [3351, 1820] 0x80000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000040020000000000000000000000000000000000000000000000000000000000000000000002000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part4189Data = true := by
  decide +kernel

theorem part4189 : Excluded (numericRows 0) 10
    ([3351, 1820] : List Nat).toFinset (checkpointSet 6 2 [2450, 2157, 3351, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part4189Ok

theorem part3832 : Excluded (numericRows 0) 10
    ([3351, 1820] : List Nat).toFinset (checkpointSet 6 2 [2157, 3351, 3058, 2752, 2437, 2136, 1820]) := by
  apply split_excluded 2450
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3834
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part4189

theorem part3582 : Excluded (numericRows 0) 10
    ([3351, 1820] : List Nat).toFinset (checkpointSet 6 2 [3351, 3058, 2752, 2437, 2136, 1820]) := by
  apply split_excluded 2157
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3584
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3832

def part4551Data : Program :=
  (.chunk 2 0xb000)

theorem part4551Ok : Numeric.run WordsX.word 909 3636 10
    [1820] 0x80000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000010000db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part4551Data = true := by
  decide +kernel

theorem part4551 : Excluded (numericRows 0) 10
    ([1820] : List Nat).toFinset (checkpointSet 6 2 [3351, 3058, 2752, 2437, 2136, 1820]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part4551Ok

theorem part3580 : Excluded (numericRows 0) 10
    ([1820] : List Nat).toFinset (checkpointSet 6 2 [3058, 2752, 2437, 2136, 1820]) := by
  apply split_excluded 3351
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3582
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part4551

theorem part2658 : Excluded (numericRows 0) 10
    ([1820] : List Nat).toFinset (checkpointSet 6 2 [2752, 2437, 2136, 1820]) := by
  apply split_excluded 3058
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2660
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3580

theorem part1874 : Excluded (numericRows 0) 10
    ([1820] : List Nat).toFinset (checkpointSet 6 2 [2437, 2136, 1820]) := by
  apply split_excluded 2752
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1876
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2658

theorem part1033 : Excluded (numericRows 0) 10
    ([1820] : List Nat).toFinset (checkpointSet 6 2 [2136, 1820]) := by
  apply split_excluded 2437
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1035
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1874

theorem part0 : Excluded (numericRows 0) 10
    ([1820] : List Nat).toFinset (checkpointSet 6 2 [1820]) := by
  apply split_excluded 2136
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1033

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (6, (0, 2)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (6, (0, 2)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 6) (j := 2) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX20

namespace MinX21

def part4Data : Program :=
  (.append
    (.append
      (.chunk 42 0x34d00021238a243106373005001df800221438a243106373005001cd00021f838a243106373005001b9c00237338a243106206005001a67002cf600295f002)
      (.append
        (.chunk 42 0x10610b005001a8b002cf6002bc100210e00023534d38a24310623c006001e1e00222334d38a24310623c006001bc400222a34d38a24310623c006001a8b002)
        (.chunk 42 0x38a24310610b373006001aae00212038a24310610b373006001a9d00210e00023538a24310610b005001e1e00222338a24310610b005001bc400222a38a243)))
    (.append
      (.chunk 42 0x243106359006001baa00220d23c38a243106359006001a6f00220623c38a243106359006001942002cdc00223c00011638a24310610b373006001e22002128)
      (.append
        (.chunk 42 0x35b006001baf00221523c38a24310635b006001a7600220b23c38a24310635b00600194a002e090020f500021b23c38a243106359006001e0100220923c38a)
        (.chunk 19 0x2200000f900022723c38a24310635b006001ce100220e23c38a243106))))

theorem part4Ok : Numeric.run WordsX.word 909 3636 10
    [2688, 2725, 2121] 0x20000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part4Data = true := by
  decide +kernel

theorem part4 : Excluded (numericRows 0) 10
    ([2688, 2725, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part4Ok

def part235Data : Program :=
  (.append
    (.append
      (.chunk 42 0x1f0ff21424323c00a006001d1800226701f0ff21423c004006001bed00201f0ff21424323c01c006001ad300201f0ff21424323c01700600199100286e002)
      (.chunk 42 0x21424323c125006001e0f00222d23921424323c125006001ce700221b23921424323c125006001a7c00221123921424323c125006001950002aab00212f000))
    (.append
      (.chunk 42 0x23c127006001e0f00222d25221424323c127006001ce700221b25221424323c127006001a7c00221125221424323c127006001950002be10020ff000226239)
      (.append
        (.chunk 42 0x6001e0f00222d24f21424323c12a006001ce700221b24f21424323c12a006001a7c00221124f21424323c12a006001950002d090020ff000226252214243)
        (.chunk 10 0x38a0000ff00022624f21424323c12a))))

theorem part235Ok : Numeric.run WordsX.word 909 3636 10
    [2997, 2725, 2121] 0x2000000000000000000000000000000000000000000000000000000000000000000020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part235Data = true := by
  decide +kernel

theorem part235 : Excluded (numericRows 0) 10
    ([2997, 2725, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part235Ok

def part413Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x23024323c00a006001d1800226701f10223023c004006001bed00201f10223024323c01c006001ad300201f10223024323c01700600199100286e002cea002)
        (.chunk 42 0x23c125006001e1200221723923024323c125006001bb800221e23923024323c125006001a7f00223923024323c125214006001953002aab00212f00001f102))
      (.append
        (.chunk 42 0x6001e1200221725223024323c127006001bb800221e25223024323c127006001a7f00225223024323c127214006001953002be1002102000229239230243)
        (.chunk 42 0xe1200221724f23024323c12a006001bb800221e24f23024323c12a006001a7f00224f23024323c12a214006001953002d0900210200022925223024323c127)))
    (.append
      (.append
        (.chunk 42 0x23c004006001bed00201f10522c24323c01c006001ad300201f10522c24323c01700600199100286e002e1500238a00010200022924f23024323c12a006001)
        (.chunk 42 0x6001bbb00222123922c24323c125006001a8200221723922c24323c125006001956002aab00212f00001f10522c24323c00a006001d1800226701f10522c))
      (.append
        (.chunk 42 0xbbb00222125222c24323c127006001a8200221725222c24323c127006001956002be100210500023323922c24323c125006001ced00221a23922c24323c125)
        (.append
          (.chunk 42 0x22124f22c24323c12a006001a8200221724f22c24323c12a006001956002d0900210500023325222c24323c127006001ced00221a25222c24323c127006001)
          (.chunk 26 0x36700038a00010500023324f22c24323c12a006001ced00221a24f22c24323c12a006001bbb002)))))

theorem part413Ok : Numeric.run WordsX.word 909 3636 10
    [2725, 2121] 0x2000000000000000000000000000000000000000000000000000000000000000000020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part413Data = true := by
  decide +kernel

theorem part413 : Excluded (numericRows 0) 10
    ([2725, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part413Ok

theorem part233 : Excluded (numericRows 0) 10
    ([2725, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 2725, 2121]) := by
  apply split_excluded 2997
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part235
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part413

theorem part2 : Excluded (numericRows 0) 10
    ([2725, 2121] : List Nat).toFinset (checkpointSet 7 0 [2725, 2121]) := by
  apply split_excluded 2688
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part4
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part233

def part779Data : Program :=
  (.append
    (.append
      (.chunk 42 0x34d00021226123f106373005001df800221426123f106373005001cd00021f826123f106373005001b9c00237326123f106206005001a67002cf600295f002)
      (.append
        (.chunk 42 0x10610b005001a8b002cf6002bc100210e00023534d26123f10623c006001e1e00222334d26123f10623c006001bc400222a34d26123f10623c006001a8b002)
        (.chunk 42 0x26123f10610b373006001aae00212026123f10610b373006001a9d00210e00023526123f10610b005001e1e00222326123f10610b005001bc400222a26123f)))
    (.append
      (.chunk 42 0x23f106359006001baa00220d23c26123f106359006001a6f00220623c26123f106359006001942002cdc00223c00011626123f10610b373006001e22002128)
      (.append
        (.chunk 42 0x35b006001baf00221523c26123f10635b006001a7600220b23c26123f10635b00600194a002e090020f500021b23c26123f106359006001e0100220923c261)
        (.chunk 19 0x2200000f900022723c26123f10635b006001ce100220e23c26123f106))))

theorem part779Ok : Numeric.run WordsX.word 909 3636 10
    [2688, 2737, 2121] 0x20020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part779Data = true := by
  decide +kernel

theorem part779 : Excluded (numericRows 0) 10
    ([2688, 2737, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part779Ok

def part1010Data : Program :=
  (.append
    (.append
      (.chunk 42 0x250ff21423f23c010006001d1e0020250ff21423f23c00a006001bf30020250ff21423f23c022006001ad90020250ff21423f23c01d006001997002874002)
      (.chunk 42 0x21423f23c002006001e0f00222d24921423f23c002006001ce700221b24921423f23c002006001a7c00221124921423f23c00200600195000297c002135000))
    (.append
      (.chunk 42 0x23c12d006001e0f00222d25821423f23c12d006001ce700221b25821423f23c12d006001a7c00221125821423f23c12d006001950002be70020ff000226249)
      (.append
        (.chunk 42 0x6001e0f00222d25521423f23c001006001ce700221b25521423f23c001006001a7c00221125521423f23c001006001950002d0f0020ff00022625821423f)
        (.chunk 10 0x2610000ff00022625521423f23c001))))

theorem part1010Ok : Numeric.run WordsX.word 909 3636 10
    [2997, 2737, 2121] 0x2000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1010Data = true := by
  decide +kernel

theorem part1010 : Excluded (numericRows 0) 10
    ([2997, 2737, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1010Ok

def part1188Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x23023f23c010006001d1e00202510223023f23c00a006001bf300202510223023f23c022006001ad900202510223023f23c01d006001997002874002cea002)
        (.chunk 42 0x23c002006001e1200221724923023f23c002006001bb800221e24923023f23c002006001a7f00224923023f23c00221400600195300297c002135000025102))
      (.append
        (.chunk 42 0x6001e1200221725823023f23c12d006001bb800221e25823023f23c12d006001a7f00225823023f23c12d214006001953002be700210200022924923023f)
        (.chunk 42 0xe1200221725523023f23c001006001bb800221e25523023f23c001006001a7f00225523023f23c001214006001953002d0f00210200022925823023f23c12d)))
    (.append
      (.append
        (.chunk 42 0x23c00a006001bf300202510522c23f23c022006001ad900202510522c23f23c01d006001997002874002e1500226100010200022925523023f23c001006001)
        (.chunk 42 0x6001bbb00222124922c23f23c002006001a8200221724922c23f23c00200600195600297c00213500002510522c23f23c010006001d1e00202510522c23f))
      (.append
        (.chunk 42 0xbbb00222125822c23f23c12d006001a8200221725822c23f23c12d006001956002be700210500023324922c23f23c002006001ced00221a24922c23f23c002)
        (.append
          (.chunk 42 0x22125522c23f23c001006001a8200221725522c23f23c001006001956002d0f00210500023325822c23f23c12d006001ced00221a25822c23f23c12d006001)
          (.chunk 26 0x36700026100010500023325522c23f23c001006001ced00221a25522c23f23c001006001bbb002)))))

theorem part1188Ok : Numeric.run WordsX.word 909 3636 10
    [2737, 2121] 0x2000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1188Data = true := by
  decide +kernel

theorem part1188 : Excluded (numericRows 0) 10
    ([2737, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1188Ok

theorem part1008 : Excluded (numericRows 0) 10
    ([2737, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 2737, 2725, 2121]) := by
  apply split_excluded 2997
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1010
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1188

theorem part777 : Excluded (numericRows 0) 10
    ([2737, 2121] : List Nat).toFinset (checkpointSet 7 0 [2737, 2725, 2121]) := by
  apply split_excluded 2688
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part779
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1008

def part1554Data : Program :=
  (.append
    (.append
      (.chunk 42 0x34d000212260256106373005001df8002214260256106373005001cd00021f8260256106373005001b9c002373260256106206005001a67002cf600295f002)
      (.append
        (.chunk 42 0x10610b005001a8b002cf6002bc100210e00023534d26025610623c006001e1e00222334d26025610623c006001bc400222a34d26025610623c006001a8b002)
        (.chunk 42 0x26025610610b373006001aae00212026025610610b373006001a9d00210e00023526025610610b005001e1e00222326025610610b005001bc400222a260256)))
    (.append
      (.chunk 42 0x256106359006001baa00220d23c260256106359006001a6f00220623c260256106359006001942002cdc00223c00011626025610610b373006001e22002128)
      (.append
        (.chunk 42 0x35b006001baf00221523c26025610635b006001a7600220b23c26025610635b00600194a002e090020f500021b23c260256106359006001e0100220923c260)
        (.chunk 19 0x2200000f900022723c26025610635b006001ce100220e23c260256106))))

theorem part1554Ok : Numeric.run WordsX.word 909 3636 10
    [2688, 3043, 2121] 0x800000000000000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1554Data = true := by
  decide +kernel

theorem part1554 : Excluded (numericRows 0) 10
    ([2688, 3043, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1554Ok

def part1785Data : Program :=
  (.append
    (.append
      (.chunk 42 0x210ff21425623c00c006001d1c0020210ff21425623c008006001bef0020210ff21425623c01e006001ad40020210ff21425623c019006001993002872002)
      (.chunk 42 0x21425623c12c006001e0f00222d24821425623c12c006001ce700221b24821425623c12c006001a7c00221124821425623c12c00600195000297a002133000))
    (.append
      (.chunk 42 0x23c127006001e0f00222d23a21425623c127006001ce700221b23a21425623c127006001a7c00221123a21425623c127006001950002aaf0020ff000226248)
      (.append
        (.chunk 42 0x6001e0f00222d25421425623c12e006001ce700221b25421425623c12e006001a7c00221125421425623c12e006001950002d0b0020ff00022623a214256)
        (.chunk 10 0x2600000ff00022625421425623c12e))))

theorem part1785Ok : Numeric.run WordsX.word 909 3636 10
    [2997, 3043, 2121] 0x800000000002000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1785Data = true := by
  decide +kernel

theorem part1785 : Excluded (numericRows 0) 10
    ([2997, 3043, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1785Ok

def part1963Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x23025623c00c006001d1c00202110223025623c008006001bef00202110223025623c01e006001ad400202110223025623c019006001993002872002cea002)
        (.chunk 42 0x23c12c006001e1200221724823025623c12c006001bb800221e24823025623c12c006001a7f00224823025623c12c21400600195300297a002133000021102))
      (.append
        (.chunk 42 0x6001e1200221723a23025623c127006001bb800221e23a23025623c127006001a7f00223a23025623c127214006001953002aaf002102000229248230256)
        (.chunk 42 0xe1200221725423025623c12e006001bb800221e25423025623c12e006001a7f00225423025623c12e214006001953002d0b00210200022923a23025623c127)))
    (.append
      (.append
        (.chunk 42 0x23c008006001bef00202110522c25623c01e006001ad400202110522c25623c019006001993002872002e1500226000010200022925423025623c12e006001)
        (.chunk 42 0x6001bbb00222124822c25623c12c006001a8200221724822c25623c12c00600195600297a00213300002110522c25623c00c006001d1c00202110522c256))
      (.append
        (.chunk 42 0xbbb00222123a22c25623c127006001a8200221723a22c25623c127006001956002aaf00210500023324822c25623c12c006001ced00221a24822c25623c12c)
        (.append
          (.chunk 42 0x22125422c25623c12e006001a8200221725422c25623c12e006001956002d0b00210500023323a22c25623c127006001ced00221a23a22c25623c127006001)
          (.chunk 26 0x36700026000010500023325422c25623c12e006001ced00221a25422c25623c12e006001bbb002)))))

theorem part1963Ok : Numeric.run WordsX.word 909 3636 10
    [3043, 2121] 0x800000000002000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1963Data = true := by
  decide +kernel

theorem part1963 : Excluded (numericRows 0) 10
    ([3043, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1963Ok

theorem part1783 : Excluded (numericRows 0) 10
    ([3043, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 3043, 2737, 2725, 2121]) := by
  apply split_excluded 2997
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1785
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1963

theorem part1552 : Excluded (numericRows 0) 10
    ([3043, 2121] : List Nat).toFinset (checkpointSet 7 0 [3043, 2737, 2725, 2121]) := by
  apply split_excluded 2688
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1554
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1783

def part2329Data : Program :=
  (.append
    (.append
      (.chunk 42 0x34d00021238c251106373005001df800221438c251106373005001cd00021f838c251106373005001b9c00237338c251106206005001a67002cf600295f002)
      (.append
        (.chunk 42 0x10610b005001a8b002cf6002bc100210e00023534d38c25110623c006001e1e00222334d38c25110623c006001bc400222a34d38c25110623c006001a8b002)
        (.chunk 42 0x38c25110610b373006001aae00212038c25110610b373006001a9d00210e00023538c25110610b005001e1e00222338c25110610b005001bc400222a38c251)))
    (.append
      (.chunk 42 0x251106359006001baa00220d23c38c251106359006001a6f00220623c38c251106359006001942002cdc00223c00011638c25110610b373006001e2200225e)
      (.append
        (.chunk 42 0x35b006001baf00221523c38c25110635b006001a7600220b23c38c25110635b00600194a002e090020f500021b23c38c251106359006001e0100220923c38c)
        (.chunk 19 0x2200000f900022723c38c25110635b006001ce100220e23c38c251106))))

theorem part2329Ok : Numeric.run WordsX.word 909 3636 10
    [2688, 3336, 2121] 0x10000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2329Data = true := by
  decide +kernel

theorem part2329 : Excluded (numericRows 0) 10
    ([2688, 3336, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 3336, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2329Ok

def part2560Data : Program :=
  (.append
    (.append
      (.chunk 42 0x1e0ff21425123c009006001d1900201e0ff21425123c005006001bec00201e0ff21425123c01b006001ad100201e0ff21425123c01600600199000286f002)
      (.chunk 42 0x21425123c129006001e0f00222d24521425123c129006001ce700221b24521425123c129006001a7c00221124521425123c129006001950002aa6002130000))
    (.append
      (.chunk 42 0x23c124006001e0f00222d23721425123c124006001ce700221b23721425123c124006001a7c00221123721425123c124006001950002aac0020ff000226245)
      (.append
        (.chunk 42 0x6001e0f00236423c22d253214251006001ce700236221b253214251128006001a7c00233e211253214251128006001950002be00020ff000226237214251)
        (.chunk 10 0x38c0000ff000361226253214251128))))

theorem part2560Ok : Numeric.run WordsX.word 909 3636 10
    [2997, 3336, 2121] 0x10000000000000000000000000000000000000000000000000000000000000000000000000800000000002000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2560Data = true := by
  decide +kernel

theorem part2560 : Excluded (numericRows 0) 10
    ([2997, 3336, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 3336, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2560Ok

def part2738Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x23025123c009006001d1900201e10223025123c005006001bec00201e10223025123c01b006001ad100201e10223025123c01600600199000286f002cea002)
        (.chunk 42 0x23c129006001e1200221724523025123c129006001bb800221e24523025123c129006001a7f00224523025123c129214006001953002aa600213000001e102))
      (.append
        (.chunk 42 0x6001e1200221723723025123c124006001bb800221e23723025123c124006001a7f00223723025123c124214006001953002aac002102000229245230251)
        (.chunk 42 0xe1200236a217253230251128006001bb800236521e253230251128006001a7f002341253230251128214006001953002be000210200022923723025123c124)))
    (.append
      (.append
        (.chunk 42 0x23c005006001bec00201e10522c25123c01b006001ad100201e10522c25123c01600600199000286f002e1500238c00010200036423c229253230251006001)
        (.chunk 42 0x6001bbb00222124522c25123c129006001a8200221724522c25123c129006001956002aa600213000001e10522c25123c009006001d1900201e10522c251))
      (.append
        (.chunk 42 0xbbb00222123722c25123c124006001a8200221723722c25123c124006001956002aac00210500023324522c25123c129006001ced00221a24522c25123c129)
        (.append
          (.chunk 42 0x36822125322c251128006001a8200234421725322c251128006001956002be000210500023323722c25123c124006001ced00221a23722c25123c124006001)
          (.chunk 26 0x36700038c00010500036a23325322c251128006001ced00236d21a25322c251128006001bbb002)))))

theorem part2738Ok : Numeric.run WordsX.word 909 3636 10
    [3336, 2121] 0x10000000000000000000000000000000000000000000000000000000000000000000000000800000000002000000000000000000000000000000000000000000000000000000000000000020020000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2738Data = true := by
  decide +kernel

theorem part2738 : Excluded (numericRows 0) 10
    ([3336, 2121] : List Nat).toFinset (checkpointSet 7 0 [2997, 2688, 3336, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2738Ok

theorem part2558 : Excluded (numericRows 0) 10
    ([3336, 2121] : List Nat).toFinset (checkpointSet 7 0 [2688, 3336, 3043, 2737, 2725, 2121]) := by
  apply split_excluded 2997
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2560
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2738

theorem part2327 : Excluded (numericRows 0) 10
    ([3336, 2121] : List Nat).toFinset (checkpointSet 7 0 [3336, 3043, 2737, 2725, 2121]) := by
  apply split_excluded 2688
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2329
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2558

def part3100Data : Program :=
  (.chunk 2 0x12b000)

theorem part3100Ok : Numeric.run WordsX.word 909 3636 10
    [2121] 0x10000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000020020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part3100Data = true := by
  decide +kernel

theorem part3100 : Excluded (numericRows 0) 10
    ([2121] : List Nat).toFinset (checkpointSet 7 0 [3336, 3043, 2737, 2725, 2121]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part3100Ok

theorem part2325 : Excluded (numericRows 0) 10
    ([2121] : List Nat).toFinset (checkpointSet 7 0 [3043, 2737, 2725, 2121]) := by
  apply split_excluded 3336
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2327
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part3100

theorem part1550 : Excluded (numericRows 0) 10
    ([2121] : List Nat).toFinset (checkpointSet 7 0 [2737, 2725, 2121]) := by
  apply split_excluded 3043
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1552
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2325

theorem part775 : Excluded (numericRows 0) 10
    ([2121] : List Nat).toFinset (checkpointSet 7 0 [2725, 2121]) := by
  apply split_excluded 2737
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part777
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1550

theorem part0 : Excluded (numericRows 0) 10
    ([2121] : List Nat).toFinset (checkpointSet 7 0 [2121]) := by
  apply split_excluded 2725
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part775

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (7, (0, 0)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (7, (0, 0)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 7) (j := 0) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX21

namespace MinX22

def part2Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x6001a76002bb600210700012323824423a21f22d006001e1300223212323824423a21f006001cee00212323824423a21f21b006001bbc002a81002aaa002)
        (.chunk 42 0xaa000223522e23824423a103006001974002cec00221500023824423a1231010ef006001dfb00223824423a12334c101006001ccf0020f923824423a123101))
      (.append
        (.chunk 42 0x23522b23824423a106006001974002e1400212300022e23824423a103385006001e3300223824423a103388251006001bdc00222e23824423a10323f006001)
        (.append
          (.chunk 42 0x6001a81002986002bdf00236600012300022b23824423a106385006001e3300223824423a106388251006001bdc00222b23824423a10623f006001aa0002)
          (.chunk 42 0x98b002ac600236600022b12600924423a26c006001e1400222e12600924423a26c006001cec00200924423a26c101215006001bb600212600924423a21f107))))
    (.append
      (.append
        (.chunk 42 0x25e246126366244260006001979002d0b00201100012636624423a276137006001d1d00213c12636624423a276006001bf800225812636624423a276006001)
        (.append
          (.chunk 42 0x263259126366244260006001be600224200036624426012611c005001e28002366244260379126005001cfc002389264366244260005001aa3002ab4002)
          (.chunk 42 0x2bb600210700012925024423a21f22d006001e1300223212925024423a21f006001cee00212925024423a21f21b006001bbc002a81002d0a00225400012e)))
      (.append
        (.chunk 42 0x22e25024423a10300600184b002cec00221500025024423a1291010ef006001dfb00225024423a12934c101006001ccf0020f925024423a129101006001a76)
        (.append
          (.chunk 42 0x24423a10600600184b002e1400212900025024423a10325f257006001be200222e25024423a103262006001ab000222e25024423a103245006001aa600223b)
          (.chunk 39 0x38b00036600012900025024423a10625f257006001be200222b25024423a106262006001ab000222b25024423a106245006001aa600223b22b250)))))

theorem part2Ok : Numeric.run WordsX.word 909 3636 10
    [2724, 2122] 0x10000000000000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2Data = true := by
  decide +kernel

theorem part2 : Excluded (numericRows 0) 10
    ([2724, 2122] : List Nat).toFinset (checkpointSet 7 1 [2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2Ok

def part465Data : Program :=
  (.append
    (.chunk 42 0x23d10f00600195e002cee00221b00036c26323d23a21f0f5006001e010020ed26323d23a21f352006001cd500236c0ff26323d23a21f006001a7c002bbc002)
    (.append
      (.chunk 42 0x6001a8e002e1300221f00036b23226323d23a0fa006001e0800236b23226323d23a0f4006001cdd00236b23226323d23a10c006001bc300234b36b232263)
      (.chunk 30 0x10700022d0000ff26323d23a21f364006001ce700236826323d23a21f119006001bce00236811126323d23a21f)))

theorem part465Ok : Numeric.run WordsX.word 909 3636 10
    [2689, 2738, 2122] 0x40010000000020000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part465Data = true := by
  decide +kernel

theorem part465 : Excluded (numericRows 0) 10
    ([2689, 2738, 2122] : List Nat).toFinset (checkpointSet 7 1 [2689, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part465Ok

def part579Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x6001a7b002ccf00210100036235c23d23a263227006001e0d00222c35c0f923d23a263006001ce800221935c0f923d23a263006001a7b002a76002bb6002)
        (.chunk 42 0xba400220735023d23a263101006001a69002dfb0021010000e723d23a26322734c006001e0d00222c0e723d23a26334c006001ce80022190e723d23a26334c))
      (.append
        (.chunk 42 0x21289006001ad700210322e23d23a01c27d006001996002875002cec0022150000ef00021a35023d23a263101006001cd600235023d23a263203101006001)
        (.append
          (.chunk 42 0x6001bd600200022e23d23a103008006001abd00297d00213600010322e23d23a00f271006001d1f00202410322e23d23a00b006001bf200210322e23d23a)
          (.chunk 42 0xd0b00225922e23d23a103242006001ab400224625922e23d23a103006001979002be600224b00038600022e23a103125006001e3100211d22e23d23a103382))))
    (.append
      (.append
        (.chunk 42 0x22e23d23a10325f002006001be200222e23d23a103002014006001ac900200c22e23d23a103002006001989002d0e00212e00025922e23d23a103254006001)
        (.chunk 42 0x6001d1f00202410622b23d23a00b006001bf200210622b23d23a021289006001ad700210622b23d23a01c27d006001996002875002e14002263000257000))
      (.append
        (.chunk 42 0x24b00038600022b23a106125006001e3100211d22b23d23a106382006001bd600200022b23d23a106008006001abd00297d00213600010622b23d23a00f271)
        (.append
          (.chunk 42 0x106002006001989002d0e00212e00025922b23d23a106254006001d0b00225922b23d23a106242006001ab400224625922b23d23a106006001979002be6002)
          (.chunk 30 0x36600026300025700022b23d23a10625f002006001be200222b23d23a106002014006001ac900200c22b23d23a)))))

theorem part579Ok : Numeric.run WordsX.word 909 3636 10
    [2738, 2122] 0x40010000000020000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part579Data = true := by
  decide +kernel

theorem part579 : Excluded (numericRows 0) 10
    ([2738, 2122] : List Nat).toFinset (checkpointSet 7 1 [2689, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part579Ok

theorem part463 : Excluded (numericRows 0) 10
    ([2738, 2122] : List Nat).toFinset (checkpointSet 7 1 [2738, 2724, 2122]) := by
  apply split_excluded 2689
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part465
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part579

def part991Data : Program :=
  (.append
    (.chunk 42 0x25510f00600195e002cee00221b00036c25e25523a21f0f5006001e010020ed25e25523a21f352006001cd500236c0ff25e25523a21f006001a7c002bbc002)
    (.append
      (.chunk 42 0x6001a8e002e1300221f00036b23225e25523a0fa006001e0800236b23225e25523a0f4006001cdd00236b23225e25523a10c006001bc300234b36b23225e)
      (.chunk 30 0x10700022d0000ff25e25523a21f364006001ce700236825e25523a21f119006001bce00236811125e25523a21f)))

theorem part991Ok : Numeric.run WordsX.word 909 3636 10
    [2689, 3044, 2122] 0x1000000000000000000000000000000000000000000000000000000000000000000000000000040010000000020000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part991Data = true := by
  decide +kernel

theorem part991 : Excluded (numericRows 0) 10
    ([2689, 3044, 2122] : List Nat).toFinset (checkpointSet 7 1 [2689, 3044, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part991Ok

def part1105Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x6001a7b002ccf00210100036235c25523a25e227006001e0d00222c35c0f925523a25e006001ce800221935c0f925523a25e006001a7b002a76002bb6002)
        (.chunk 42 0xba400220735025523a25e101006001a69002dfb0021010000e725523a25e22734c006001e0d00222c0e725523a25e34c006001ce80022190e725523a25e34c))
      (.append
        (.chunk 42 0x23a01f006001ad600202210322e25523a01a006001994002871002cec0022150000ef00021a35025523a25e101006001cd600235025523a25e203101006001)
        (.append
          (.chunk 42 0x6001be600224622e25523a103242006001ab400297900213200002210322e25523a00d006001d1b00202210322e25523a007006001bf000202210322e255)
          (.chunk 42 0xe2200222e25523a103373128006001cf600212022e25523a103128006001a9d002aae00212e00024622e25523a103254006001d0b00224622e25523a103263))))
    (.append
      (.append
        (.chunk 42 0x21625222e25523a12d006001bba00225222e25523a12d364006001a7d00221325222e25523a12d006001952002d0c00223c00037725523a103128116006001)
        (.append
          (.chunk 42 0x6001bf000202210622b25523a01f006001ad600202210622b25523a01a006001994002871002e1400225e00010300022825222e25523a12d006001e11002)
          (.chunk 42 0xd0b00224622b25523a106263006001be600224622b25523a106242006001ab400297900213200002210622b25523a00d006001d1b00202210622b25523a007)))
      (.append
        (.chunk 42 0x22b25523a106128116006001e2200222b25523a106373128006001cf600212022b25523a106128006001a9d002aae00212e00024622b25523a106254006001)
        (.append
          (.chunk 42 0x22b25523a12d006001cef00221925222b25523a12d006001bbd00225222b25523a12d367006001a8000221625222b25523a12d006001955002d0c00223c000)
          (.chunk 8 0x36600025e000106000231252)))))

theorem part1105Ok : Numeric.run WordsX.word 909 3636 10
    [3044, 2122] 0x1000000000000000000000000000000000000000000000000000000000000000000000000000040010000000020000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1105Data = true := by
  decide +kernel

theorem part1105 : Excluded (numericRows 0) 10
    ([3044, 2122] : List Nat).toFinset (checkpointSet 7 1 [2689, 3044, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1105Ok

theorem part989 : Excluded (numericRows 0) 10
    ([3044, 2122] : List Nat).toFinset (checkpointSet 7 1 [3044, 2738, 2724, 2122]) := by
  apply split_excluded 2689
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part991
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1105

def part1537Data : Program :=
  (.append
    (.chunk 42 0x24f10f00600195e002cee00221b00036c38a24f23a21f0f5006001e010020ed38a24f23a21f352006001cd500236c0ff38a24f23a21f006001a7c002bbc002)
    (.append
      (.chunk 42 0x6001a8e002e1300221f00036b23238a24f23a0fa006001e0800236b23238a24f23a0f4006001cdd00236b23238a24f23a10c006001bc300234b36b23238a)
      (.chunk 30 0x10700022d0000ff38a24f23a21f364006001ce700236838a24f23a21f119006001bce00236811138a24f23a21f)))

theorem part1537Ok : Numeric.run WordsX.word 909 3636 10
    [2689, 3337, 2122] 0x20000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000040010000000020000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1537Data = true := by
  decide +kernel

theorem part1537 : Excluded (numericRows 0) 10
    ([2689, 3337, 2122] : List Nat).toFinset (checkpointSet 7 1 [2689, 3337, 3044, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1537Ok

def part1651Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x6001a7b002ccf00210100036235c24f23a38a227006001e0d00222c35c0f924f23a38a006001ce800221935c0f924f23a38a006001a7b002a76002bb6002)
        (.chunk 42 0xba400220735024f23a38a101006001a69002dfb0021010000e724f23a38a22734c006001e0d00222c0e724f23a38a34c006001ce80022190e724f23a38a34c))
      (.append
        (.chunk 42 0x23a01c006001ad300201f10322e24f23a01700600199100286e002cec0022150000ef00021a35024f23a38a101006001cd600235024f23a38a203101006001)
        (.append
          (.chunk 42 0x6001be300224322e24f23a10323f006001ab1002aa500212f00001f10322e24f23a00a006001d1800201f10322e24f23a004006001bed00201f10322e24f)
          (.chunk 42 0xe1f00222e24f23a103370125006001cf300211d22e24f23a103125006001a9a002aab00212b00024322e24f23a103251006001d0800225624322e24f23a103))))
    (.append
      (.append
        (.chunk 42 0x36b21625222e24f127006001bba00221d25222e24f127364006001a7d00233f21325222e24f127006001952002be100223900022e24f23a103125113006001)
        (.append
          (.chunk 42 0x6001bed00201f10622b24f23a01c006001ad300201f10622b24f23a01700600199100286e002e1400238a00010300036323a22825222e24f006001e11002)
          (.chunk 42 0xd0800225624322b24f23a106006001be300224322b24f23a10623f006001ab1002aa500212f00001f10622b24f23a00a006001d1800201f10622b24f23a004)))
      (.append
        (.chunk 42 0x37424f23a106125113006001e1f00222b24f23a106370125006001cf300211d22b24f23a106125006001a9a002aab00212b00024322b24f23a106251006001)
        (.append
          (.chunk 42 0x25222b24f127006001cef00236e21925222b24f127006001bbd00222025222b24f127367006001a8000234221625222b24f127006001955002be1002239000)
          (.chunk 8 0x36600038a000106000369231)))))

theorem part1651Ok : Numeric.run WordsX.word 909 3636 10
    [3337, 2122] 0x20000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000040010000000020000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1651Data = true := by
  decide +kernel

theorem part1651 : Excluded (numericRows 0) 10
    ([3337, 2122] : List Nat).toFinset (checkpointSet 7 1 [2689, 3337, 3044, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1651Ok

theorem part1535 : Excluded (numericRows 0) 10
    ([3337, 2122] : List Nat).toFinset (checkpointSet 7 1 [3337, 3044, 2738, 2724, 2122]) := by
  apply split_excluded 2689
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1537
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1651

def part2079Data : Program :=
  (.chunk 2 0x12a000)

theorem part2079Ok : Numeric.run WordsX.word 909 3636 10
    [2122] 0x20000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000040010000000000000000000000000000000000000000000000000000000000000000000000000002492492492492492492492492492492492492492492492492492492492492492492492492497ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2079Data = true := by
  decide +kernel

theorem part2079 : Excluded (numericRows 0) 10
    ([2122] : List Nat).toFinset (checkpointSet 7 1 [3337, 3044, 2738, 2724, 2122]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2079Ok

theorem part1533 : Excluded (numericRows 0) 10
    ([2122] : List Nat).toFinset (checkpointSet 7 1 [3044, 2738, 2724, 2122]) := by
  apply split_excluded 3337
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1535
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2079

theorem part987 : Excluded (numericRows 0) 10
    ([2122] : List Nat).toFinset (checkpointSet 7 1 [2738, 2724, 2122]) := by
  apply split_excluded 3044
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part989
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1533

theorem part461 : Excluded (numericRows 0) 10
    ([2122] : List Nat).toFinset (checkpointSet 7 1 [2724, 2122]) := by
  apply split_excluded 2738
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part463
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part987

theorem part0 : Excluded (numericRows 0) 10
    ([2122] : List Nat).toFinset (checkpointSet 7 1 [2122]) := by
  apply split_excluded 2724
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part461

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (7, (0, 1)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (7, (0, 1)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 7) (j := 1) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX22

namespace MinX23

def part2Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x6001982002be900226700038c23b36825b249261006001d1500223b36800412f249261006001bed00223b36800826124924f00600198200297c002ab7002)
        (.chunk 42 0xbed00238c23b36800825724f006001982002d0e00226700038c26623b36800725b006001d1500238c26623b36800412f006001bed00225c38c23b36800824f))
      (.append
        (.chunk 42 0x37e246006001d0400223538c11723b36822e006001bd2002a95002cff00200200026700026323b36800725b257006001d1500226323b36800412f257006001)
        (.append
          (.chunk 42 0x5001e0700238c11723b0f3358005001cdb00238c11723b37210d005001bc2002a82002bca00211b00038c11723b36837b240006001e2900238c11723b368)
          (.chunk 42 0xa7e002ceb00221300011711434e1000ee005001dfc00211711434b1000e8005001cd100211711435a1000fb005001a75002bb700222100010538c11723b0fb))))
    (.append
      (.append
        (.chunk 42 0x5001bce00211138c117114107005001a8e002e1300210400022f38c11711422a005001e1000238c117114369218005001bb900238c11711436321c005001)
        (.append
          (.chunk 42 0xceb00238c11723b11a100213006001bb700211a24138c11723b221006001a82002e2a00236800022d00038c117114364107005001ce700211711437e107119)
          (.chunk 42 0x124005001d0400238023b11912422d005001bce002aac002a99002e2b00237c00036800038c11723b11a10722d006001e1300224138c11723b11a104006001)))
      (.append
        (.chunk 42 0x1a94002bd400223700023b36837238c11237e006001e2000223b36836f38c10c37e006001cf500237e00023b36811e243124005001e2c00223b36811b246)
        (.append
          (.chunk 42 0x238324a38c38023b221006001a82002bd700223300038c38023b36838410d006001e1900238c38023b36836a384006001ced00238c38023b368384117006)
          (.chunk 35 0x24500011f00036800038c38023b38310722d006001e1300224a38c38023b383104006001ceb00238c38023b383100213006001bb7)))))

theorem part2Ok : Numeric.run WordsX.word 909 3636 10
    [2726, 2123] 0x40000000000000000000000000000000000000000000000000000000000000000000000000006db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6dbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2Data = true := by
  decide +kernel

theorem part2 : Excluded (numericRows 0) 10
    ([2726, 2123] : List Nat).toFinset (checkpointSet 7 2 [2726, 2123]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2Ok

def part459Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x600198e002bea00224300024a23e23b36837e11e006001e2c00224a23e23b36837b118006001d0100224a23e23b36838a12b006001aa5002ab800297b002)
        (.chunk 42 0xaca00223e23b36826d26100e006001988002d0f00225b00023e23b368267264007006001d1500224a23e23b368264019006001ad000223e23b368273264014))
      (.append
        (.chunk 42 0x100213006001bb700210527200f23e23b221006001a8200298c002be500200100025500023e23b36825e26112a006001be400224a23e23b368261013006001)
        (.chunk 42 0x6001bfe00236823e23b27612f27c006001991002acc00236800000f23e23b27210722d006001e1300222f00f23e23b272104006001ceb00200f23e23b272)))
    (.append
      (.append
        (.chunk 42 0xbec00236823e23b26626a248006001aba00236823e23b26626424c00600197f002d1100201700027836823e23b13d27c006001d2300227b14236823e23b27c)
        (.chunk 42 0x23b0fb006001e0700200025623e23b0f3358006001cdb00200025623e23b37210d006001bc2002a82002d1000225a00000500026913036823e23b266006001))
      (.append
        (.chunk 42 0xceb00221300023e23b00034e1000ee006001dfc00223e23b00034b1000e8006001cd100223e23b00035a1000fb006001a75002bb700222100010500025623e)
        (.append
          (.chunk 42 0x23e23b000107006001a8e002e1300210400022f25623e23b00022a006001e1000225623e23b000369218006001bb900225623e23b00036321c006001a7e002)
          (.chunk 28 0x26200036800022d00025623e23b000364107006001ce700223e23b00037e107119006001bce002111256)))))

theorem part459Ok : Numeric.run WordsX.word 909 3636 10
    [2736, 2123] 0x10040000000000000000000000000000000000000000000000000000000000000000000000000006db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6dbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part459Data = true := by
  decide +kernel

theorem part459 : Excluded (numericRows 0) 10
    ([2736, 2123] : List Nat).toFinset (checkpointSet 7 2 [2736, 2726, 2123]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part459Ok

def part825Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0xfb005001a75002bb700222100010526f00c1260fb005001e0700226f00c1260f3358005001cdb00226f00c12637210d005001bc2002a82002aad002989002)
        (.append
          (.chunk 42 0x26f369218005001bb900200c12626f36321c005001a7e002ceb00221300012626f34e1000ee005001dfc00212626f34b1000e8005001cd100212626f35a100)
          (.chunk 42 0xc12626f364107005001ce700212626f37e107119005001bce00211100c12626f107005001a8e002e1300210400022f00c12626f22a005001e1000200c126)))
      (.append
        (.chunk 42 0xa9b002d0d00223b00011400c36826f37612d006001e2400224700c36826f12d110006001cf700200c36826f38212d121006001a9b00297800236800022d000)
        (.append
          (.chunk 42 0x25f13200600199400298e002ac900225f00023b00025311400c36826f376006001e2400212c25300c36826f110006001cf700225300c36826f382121006001)
          (.chunk 42 0x13813e25f019005001d2100201013b13e25f019005001bf900200e13e25b25f251005001ac3002d2700236801614125b25f273006001bff00236801a27325b))))
    (.append
      (.append
        (.chunk 42 0x2d2000227900013f36827801913e25f006001d2700213f36827801614125f006001bff00227813f36801a25f132006001994002bfb002279000273000368)
        (.append
          (.chunk 42 0x1ab1002aad00297c002d0e00201400027900036827501913e13a25f006001d2700236827501614113a25f006001bff00227536801a13a25f132006001994)
          (.chunk 42 0x261249006001d0d00224736826323b261249006001978002261000368263001255249005001d0f00236826312d258249005001be700236826312b24923f005)))
      (.append
        (.chunk 42 0x266126368136005001875002aad002be900224500038036826326711f25f006001e2b00211736826337c26725f006001cff002ab700225f00025336826323b)
        (.append
          (.chunk 42 0xd0d00224726336825c12d23b00600197800226300026612636825c12e005001be600212636825c12a23d005001ab200226612636825c24b00500197d00225c)
          (.chunk 14 0x25700000200025f00025326626336825c23b006001)))))

theorem part825Ok : Numeric.run WordsX.word 909 3636 10
    [3042, 2123] 0x400000000000000000000000000000000000000000000000000000000000000000000000000010040000000000000000000000000000000000000000000000000000000000000000000000000006db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6dbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part825Data = true := by
  decide +kernel

theorem part825 : Excluded (numericRows 0) 10
    ([3042, 2123] : List Nat).toFinset (checkpointSet 7 2 [3042, 2736, 2726, 2123]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part825Ok

def part1301Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x988002be400223d00024425036823b378118006001e2600224425036823b375112006001cfb00226324436823b384125006001a9f002ab2002aa4002d0a002)
        (.chunk 42 0x25036823b26738a008006001982002d0900225500025036823b26125e001006001d0f00224425036823b25e013006001aca00225036823b26d25e00e006001))
      (.append
        (.chunk 42 0x6001bdb002123238250368234382006001aa9002a9b002aaa00212a00024f00025036823b38738a124006001bde00224425036823b38a00d006001ac4002)
        (.append
          (.chunk 42 0x25f00012c253123250368126006001d0d00224712325036812612d006001978002aad002121000238250368381246382006001e2f00223825036838424c382)
          (.chunk 42 0x114115006001a8f002e24002110000123238250368374236006001e1c002238250368374375224006001bc500223825036837436f228006001a8a002cf7002))))
    (.append
      (.append
        (.chunk 42 0x368114123119005001e2500236811426112312b005001ab1002386238250368114005001aa0002cf9002223123238250368114006001bc4002123238250368)
        (.chunk 42 0x36826c382126121006001a9b00225f00025300925036826c005001d0d00200925036826c12d005001978002aad002986002bdf00223b00037600023f000250))
      (.append
        (.chunk 42 0x250368276006001bf800212625036827025827600600198b002ac600223b00000925036826c376126006001e2400200925036826c126110006001cf7002250)
        (.append
          (.chunk 42 0x260006001be600223b250368260264242006001ab400212625036826025e246006001979002d0b002011000272126250368137276006001d1d00227513c126)
          (.chunk 13 0x12900038b00025400012e000263259126250368)))))

theorem part1301Ok : Numeric.run WordsX.word 909 3636 10
    [2123] 0x400000000000000000000000000000000000000000000000000000000000000000000000000010040000000000000000000000000000000000000000000000000000000000000000000000000006db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6dbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part1301Data = true := by
  decide +kernel

theorem part1301 : Excluded (numericRows 0) 10
    ([2123] : List Nat).toFinset (checkpointSet 7 2 [3042, 2736, 2726, 2123]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part1301Ok

theorem part823 : Excluded (numericRows 0) 10
    ([2123] : List Nat).toFinset (checkpointSet 7 2 [2736, 2726, 2123]) := by
  apply split_excluded 3042
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part825
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part1301

theorem part457 : Excluded (numericRows 0) 10
    ([2123] : List Nat).toFinset (checkpointSet 7 2 [2726, 2123]) := by
  apply split_excluded 2736
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part459
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part823

theorem part0 : Excluded (numericRows 0) 10
    ([2123] : List Nat).toFinset (checkpointSet 7 2 [2123]) := by
  apply split_excluded 2726
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part457

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (7, (0, 2)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (7, (0, 2)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 7) (j := 2) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX23

namespace MinX24

def part2Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x266240382006001bdb002382000266240234389247005001bd6002266240234389247005001bd0002234266240120389005001e30002aa9002a9b002aad002)
        (.chunk 42 0x374006001e1c002224126266240247374006001bc5002228126266240247374006001a8a002cf7002121000381246126266240382006001e2f00238424c126))
      (.append
        (.chunk 42 0x114000379126266240247376006001cfc002229126266240247376006001bca002230126266240247376006001a91002e24002110000236126266240247)
        (.append
          (.chunk 42 0x389240005001aae002387129257247389005001aa2002d05002385003129257240120006001bd900227012925724024700b006001ac0002980002be200223b)
          (.chunk 42 0x6001d0a00226223e25c240247002006001ab000224525738c25c240247006001aa6002be900224e000128000129257247389240005001be0002129257247))))
    (.append
      (.append
        (.chunk 42 0x12900025025a257240247005006001d0a00223e25a257240247005006001ab000224525a257240247005006001aa6002d1100212900038b25025c240247002)
        (.chunk 42 0x240005001be000238712c253247389005001aa2002d0500238500312c253240120006001bd900227012c25324024700b006001ac0002980002d0d002266000))
      (.append
        (.chunk 42 0x1be500224125c240253247002006001ab300224825c24025324700200600197a002be900224e00012800012c247389253240005001aae00238c12c247389)
        (.append
          (.chunk 42 0x5000130240253247262005001bec002248240253247262005001aba00224c24025324726200500197f002be5002d1100212c00025a25c240253247002006)
          (.chunk 26 0x25f00026600012c00024100524025324725a006001ab300226000524025324725a00600197a002)))))

theorem part2Ok : Numeric.run WordsX.word 909 3636 10
    [2741, 2424] 0x20000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2Data = true := by
  decide +kernel

theorem part2 : Excluded (numericRows 0) 10
    ([2741, 2424] : List Nat).toFinset (checkpointSet 8 0 [2741, 2424]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2Ok

def part408Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x261258382006001bdb002382000261258234389247005001bd6002261258234389247005001bd0002234261258120389005001e30002aa9002a9b002aad002)
        (.chunk 42 0x374006001e1c002224126261258247374006001bc5002228126261258247374006001a8a002cf7002121000381246126261258382006001e2f00238424c126))
      (.append
        (.chunk 42 0x114000379126261258247376006001cfc002229126261258247376006001bca002230126261258247376006001a91002e24002110000236126261258247)
        (.chunk 42 0x1aa6002ab1002249000384129257258247124006001e3200238112925725824711e006001bd800226f002129258247007006001abe00297c002be200223b)))
    (.append
      (.append
        (.chunk 42 0x2245255257258247001006001aa6002d0f00212900025023f25725824712b006001d0a00223e23f25725824712b006001ab000224523f25725824712b006)
        (.chunk 42 0x11e006001bd800200212c253258247007006001abe00297c002d0d002261000129000250255257258247001006001d0a00223e255257258247001006001ab0))
      (.append
        (.chunk 42 0x1be500224123f25325824712b006001ab300224823f25325824712b00600197a002ab100224900000212c253258247124006001e3200200212c253258247)
        (.append
          (.chunk 42 0x25a255253258247001006001be5002241255253258247001006001ab300224825525325824700100600197a002d0f00212c00025a23f25325824712b006)
          (.chunk 5 0x25f00026100012c)))))

theorem part408Ok : Numeric.run WordsX.word 909 3636 10
    [3047, 2424] 0x800000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part408Data = true := by
  decide +kernel

theorem part408 : Excluded (numericRows 0) 10
    ([3047, 2424] : List Nat).toFinset (checkpointSet 8 0 [3047, 2741, 2424]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part408Ok

def part749Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0x382006001bdb00238200025e252234389247005001bd600225e252234389247005001bd000223425e252120389005001e30002aa9002a9b002aad002d0c002)
        (.chunk 42 0xa8a002cf7002121000382000126252246381247005001bd6002126252246381247005001bd000212625e252120381005001e30002e2f00238424c12625e252))
      (.append
        (.chunk 42 0x23012625e252247376006001a91002e2400211000023612625e252247374006001e1c00222412625e252247374006001bc500222812625e252247374006001)
        (.chunk 42 0x6001d0400212e129257252247004006001abb002979002be200223b00011400037912625e252247376006001cfc00222912625e252247376006001bca002)))
    (.append
      (.append
        (.chunk 42 0xd0a00223e23c257252247128006001ab000224523c257252247128006001aa6002aae00224600012e129257252247121006001e2f00212e12925725224711b)
        (.chunk 42 0x25025525725224712a006001d0a00223e25525725224712a006001ab000224525525725224712a006001aa6002be400212900025023c257252247128006001))
      (.append
        (.chunk 42 0xaae00224600012e12c253252247121006001e2f00212e12c25325224711b006001d0400212e12c253252247004006001abb002979002d0d00225e000129000)
        (.append
          (.chunk 42 0x25325224712a00600197a002be400212c00026225a23c252247128006001be500226524123c252247128006001ab300226024823c25224712800600197a002)
          (.chunk 30 0x12d00025f00025e00012c00025a25525325224712a006001be500224125525325224712a006001ab3002248255)))))

theorem part749Ok : Numeric.run WordsX.word 909 3636 10
    [2424] 0x800000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part749Data = true := by
  decide +kernel

theorem part749 : Excluded (numericRows 0) 10
    ([2424] : List Nat).toFinset (checkpointSet 8 0 [3047, 2741, 2424]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part749Ok

theorem part406 : Excluded (numericRows 0) 10
    ([2424] : List Nat).toFinset (checkpointSet 8 0 [2741, 2424]) := by
  apply split_excluded 3047
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part408
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part749

theorem part0 : Excluded (numericRows 0) 10
    ([2424] : List Nat).toFinset (checkpointSet 8 0 [2424]) := by
  apply split_excluded 2741
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part406

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (8, (0, 0)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (8, (0, 0)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 8) (j := 0) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX24

namespace MinX25

def part2Data : Program :=
  (.append
    (.append
      (.chunk 42 0x6001bc1002cf6002120000264242246383382247006001e30002128264242246383385006001bd9002264242246383388235006001aa7002a9d002aae002)
      (.append
        (.chunk 42 0xcfd00222a128264242246377006001bcb00222e128264242246377006001a90002e2200237300012826424224610e238006001e2100212826424224610e220)
        (.chunk 42 0x263004006001d1200225b23d242246263001006001bea00226323d25524224624c00600197f002ab2002be400223c000116000128264242246377241006001)))
    (.append
      (.append
        (.chunk 42 0x12a00026400025824f25524238a004006001d1200225b24f24224638a001006001bea00238a24f25524224624c00600197f002d0900226400025823d255242)
        (.chunk 42 0xabb002d12002be7002264000258240252242266004006001d12002240252242246266001006001bea00226624025224224624c00600197f002ab5002d0c002))
      (.append
        (.chunk 42 0x25800600197f00200400012f261242252246005001bed00226100025226c001255004001d0f00223f24225226c004001ab100226c24225224900400197c002)
        (.chunk 21 0x25e00012d00026400025b242252246001258006001bea00224c261242252246))))

theorem part2Ok : Numeric.run WordsX.word 909 3636 10
    [2740, 2425] 0x1000124924924924924924924924924924924924924924924924924924924924924924924924924bffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part2Data = true := by
  decide +kernel

theorem part2 : Excluded (numericRows 0) 10
    ([2740, 2425] : List Nat).toFinset (checkpointSet 8 1 [2740, 2425]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part2Ok

def part275Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0xae3002d2b00224600001814626301525e121006001e2f00201814626301525e11b006001d0400201814626301525e004006001abb002c00002acb002be6002)
        (.chunk 42 0x24637c006001e2a00212c11626300325e246006001cfd002ab3002d1300227d00014200001b01726301525e246006001bfe00202d26301525e246295006001))
      (.append
        (.chunk 42 0x26500024600038125d26300325e121006001e2f00237e25d26300325e11b006001d0400226c25d26300325e004006001abb002be800224100011a26300325e)
        (.chunk 42 0x1bef00226700026000925e12f007005001d1500224526000925e12f005001ab700212f26000925e24f005001982002986002bed002abb002d0b002259000)))
    (.append
      (.append
        (.chunk 42 0x25b25826025e254001006001bea00200524c25826025e25400600197f002d1200226c00013126026725e12f254006001d1700226026725e12f133254006)
        (.chunk 42 0x2e2900225400022e26037e25e12638b006001bdf00238322e26037e25e011006001ac600222e26037e25e00926c006001986002bd2002d04002004000264))
      (.append
        (.chunk 42 0x26c006001986002aa9002e2f00211b00025400024026037e25e12638b006001bdf00237b24026037e25e011006001ac600224026037e25e00926c006001986)
        (.append
          (.chunk 42 0x1ac600224c26038125e00926c006001986002bdb00225400023426038125e12638b006001bdf00238923426038125e011006001ac600223426038125e009)
          (.chunk 25 0x12e00024600012100025400024c26038125e12638b006001bdf00238424c26038125e011006)))))

theorem part275Ok : Numeric.run WordsX.word 909 3636 10
    [2425] 0x1000124924924924924924924924924924924924924924924924924924924924924924924924924bffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part275Data = true := by
  decide +kernel

theorem part275 : Excluded (numericRows 0) 10
    ([2425] : List Nat).toFinset (checkpointSet 8 1 [2740, 2425]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part275Ok

theorem part0 : Excluded (numericRows 0) 10
    ([2425] : List Nat).toFinset (checkpointSet 8 1 [2425]) := by
  apply split_excluded 2740
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part2
  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using part275

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (8, (0, 1)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (8, (0, 1)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 8) (j := 1) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX25

namespace MinX26

def part0Data : Program :=
  (.append
    (.append
      (.append
        (.chunk 42 0xd1300237723c25d37a248260006001be8002e2200226500022a37a24826025937b006001d1300222a25d37a24826037b006001be8002bcb002cfd002ab3002)
        (.chunk 42 0xbca002d1300237c00011724500025d248260006001cff00211400025d248260229006001bca002be8002e2a00211600026500023c37737a248260259006001))
      (.append
        (.chunk 42 0xe1f00212937725a248260378006001bc8002cfa002ab0002be500224100026500037c000117245003248260259006001cff002114003248260259229006001)
        (.chunk 42 0xab1002be3002d1000223e00037900024212911725a248260006001cfc00212911725a248260226006001bc7002e2700211300023912937725a248260006001)))
    (.append
      (.append
        (.chunk 42 0xbe800225a24838c268244005001ab600224b25125a24838c00500197d002d0800226100025a248000001255005001d0f00225a24800012d258005001be7002)
        (.chunk 42 0x2d0d00226200025600026000001225a24800012e27a006001d0b00225a24800012727a23a006001aaf002ac800212b00000000025125a24838c265005001))
      (.append
        (.chunk 42 0x13c006001d2500212925714000f248260006001bfa002be200223b00011400f248260376277006001e2400212600f248260277110006001cf7002aad002ac5)
        (.append
          (.chunk 42 0x25e006001aae002be200223b00038c114248260376128006001e2400212638c248260128110006001cf7002aad002be000225f00027700025712900f248260)
          (.chunk 23 0x12c00025300025f00012800038924e25738c248260006001d0500223c25738c248260)))))

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [2426] 0x36db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6dfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([2426] : List Nat).toFinset (checkpointSet 8 2 [2426]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (8, (0, 2)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (8, (0, 2)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 8) (j := 2) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX26

namespace MinX27

def part0Data : Program :=
  (.append
    (.append
      (.chunk 42 0xbe300226123f38524e23538c006001ab1002d0800200e00026f13438524e235273006001d1a00227213938524e235273006001bf5002ac3002bdc002bd9002)
      (.chunk 42 0xaaa002e3300223200011d12624d24e23510b006001e1b00211d12624d24e235107006001cee002bd3002d0700225100012b00026025638524e23538c006001))
    (.append
      (.chunk 42 0xe000134123382247235273006001d1a002139123382247235273006001bf5002ac3002bdc002e3000238800038500012300023824a24d24e235126006001)
      (.append
        (.chunk 42 0xe1800211a12624d247235104006001ceb002bd0002d0700225100012b00025612338224723538c006001be300223f12338224723538c006001ab1002d08002)
        (.chunk 40 0x12000038800038200012600025424b24d24723511d006001bdf00223b24b24d24723511d006001aad002bd600222f00011a12624d247235108006001))))

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [2727] 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([2727] : List Nat).toFinset (checkpointSet 9 0 [2727]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (9, (0, 0)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (9, (0, 0)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 9) (j := 0) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX27

namespace MinX28

def part0Data : Program :=
  (.append
    (.chunk 42 0x6001d1b002138124383248236275006001bf6002ac4002bde002e2e00224d00012600038800038625123638712338b006001bdc002bdf002d07002bda002)
    (.append
      (.chunk 42 0x6001cec002bd2002d0600224f00012a00025512438324823638a006001be400223d12438324823638a006001ab2002d0900200d000132124383248236275)
      (.chunk 38 0x12200038700038300024a00024c248236127385123006001e33002bd700222e00011b12724c248236109006001e1700211b12724c248236103)))

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [2728] 0x924924924924924924924924924924924924924924924924924924924924924924924924925ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([2728] : List Nat).toFinset (checkpointSet 9 1 [2728]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (9, (0, 1)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (9, (0, 1)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 9) (j := 1) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX28

namespace MinX29

def part0Data : Program :=
  (.append
    (.chunk 42 0xbdd002bd8002e2f00238400038900024e00024c234124385128120006001bd9002d0500225000024924c23438b125129006001d0a002bdd002e32002bdb002)
    (.chunk 32 0x12100038100038900024e00024623411e385128120006001bd9002d0500225000024924623438b125129006001d0a002))

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [2729] 0x1b6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([2729] : List Nat).toFinset (checkpointSet 9 2 [2729]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (9, (0, 2)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (9, (0, 2)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 9) (j := 2) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX29

namespace MinX30

def part0Data : Program :=
  (.chunk 24 0x11d00038200024700011c00024212037f24424b380006001e28002d03002e30002e2d002)

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [3030] 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([3030] : List Nat).toFinset (checkpointSet 10 0 [3030]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (10, (0, 0)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (10, (0, 0)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 10) (j := 0) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX30

namespace MinX31

def part0Data : Program :=
  (.chunk 6 0x11f000245000e2b002)

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [3031] 0x492492492492492492492492492492492492492492492492492492492492492492492492492ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([3031] : List Nat).toFinset (checkpointSet 10 1 [3031]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (10, (0, 1)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (10, (0, 1)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 10) (j := 1) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX31

namespace MinX32

def part0Data : Program :=
  (.chunk 30 0x11e00038100024600011b00012100037b00024c240118384004001d01002bdb002e29002d04002e2f002e2c002)

theorem part0Ok : Numeric.run WordsX.word 909 3636 10
    [3032] 0xdb6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff part0Data = true := by
  decide +kernel

theorem part0 : Excluded (numericRows 0) 10
    ([3032] : List Nat).toFinset (checkpointSet 10 2 [3032]) := by
  exact checkedNumericPart WordsX.correct (by decide) (by decide)
    (by decide +kernel) part0Ok

/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : (10, (0, 2)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (10, (0, 2)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained 0)) s) (hw : s.card ≤ 10) : False := by
  apply min_from_root (b := 10) (j := 2) _ ha hm hz hw
  exact part0

#print axioms verified

end MinX32

end ArmillaryLean.Code8749
