import Wire

/-!
# New York Stock Exchange Deep Feed v1.3.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseArcaoptionsDeepfeedXdpV13A

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive QuoteCondition where
  | regularTrading -- Regular Trading
  | rotation -- Rotation
  | tradingHalted -- Trading Halted
  | preopen -- Preopen
  | rotationLegalWidthQuotePending -- Rotation Legal Width Quote Pending
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularTrading => 0x31
  | .rotation => 0x32
  | .tradingHalted => 0x33
  | .preopen => 0x34
  | .rotationLegalWidthQuotePending => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x31 then .regularTrading
  else if byte = 0x32 then .rotation
  else if byte = 0x33 then .tradingHalted
  else if byte = 0x34 then .preopen
  else .rotationLegalWidthQuotePending

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularTrading => decide
  | rotation => decide
  | tradingHalted => decide
  | preopen => decide
  | rotationLegalWidthQuotePending => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x4C, 0x4E, 0x4F, 0x58, 0x53, 0x55, 0x54, 0x51]

inductive SecurityStatus where
  | lightUpADarkSeries -- Light Up A Dark Series
  | openADarkSeries -- Open A Dark Series
  | open_ -- Open
  | close -- Close
  | halt -- Halt
  | unhalt -- Unhalt
  | unhaltADarkSeries -- Unhalt A Dark Series
  | endOfRfqAuction -- End Of Rfq Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .lightUpADarkSeries => 0x4C
  | .openADarkSeries => 0x4E
  | .open_ => 0x4F
  | .close => 0x58
  | .halt => 0x53
  | .unhalt => 0x55
  | .unhaltADarkSeries => 0x54
  | .endOfRfqAuction => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x4C then .lightUpADarkSeries
  else if byte = 0x4E then .openADarkSeries
  else if byte = 0x4F then .open_
  else if byte = 0x58 then .close
  else if byte = 0x53 then .halt
  else if byte = 0x55 then .unhalt
  else if byte = 0x54 then .unhaltADarkSeries
  else .endOfRfqAuction

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | lightUpADarkSeries => decide
  | openADarkSeries => decide
  | open_ => decide
  | close => decide
  | halt => decide
  | unhalt => decide
  | unhaltADarkSeries => decide
  | endOfRfqAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x4E, 0x50, 0x51, 0x41, 0x31, 0x32]

inductive ExchangeCode where
  | nyse -- Nyse
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | nyseMkt -- Nyse Mkt
  | globalOtc -- Global Otc
  | arcaLocalNontapebIndex -- Arca Local Nontapeb Index
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .nyse => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .nyseMkt => 0x41
  | .globalOtc => 0x31
  | .arcaLocalNontapebIndex => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x4E then .nyse
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x41 then .nyseMkt
  else if byte = 0x31 then .globalOtc
  else .arcaLocalNontapebIndex

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | nyse => decide
  | nyseArca => decide
  | nasdaq => decide
  | nyseMkt => decide
  | globalOtc => decide
  | arcaLocalNontapebIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x41, 0x43, 0x44, 0x45, 0x46, 0x48, 0x49, 0x4D, 0x4F, 0x50, 0x52, 0x53, 0x54, 0x55, 0x57, 0x58]

inductive SecurityType where
  | adr -- Adr
  | commonStock -- Common Stock
  | debentures -- Debentures
  | etf -- Etf
  | foreign -- Foreign
  | americanDepositoryShares -- American Depository Shares
  | units -- Units
  | miscliquidTrust -- Miscliquid Trust
  | ordinaryShares -- Ordinary Shares
  | preferredStock -- Preferred Stock
  | rights -- Rights
  | sharesOfBeneficiaryInterest -- Shares Of Beneficiary Interest
  | test -- Test
  | units_55 -- Units
  | warrant -- Warrant
  | index -- Index
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .adr => 0x41
  | .commonStock => 0x43
  | .debentures => 0x44
  | .etf => 0x45
  | .foreign => 0x46
  | .americanDepositoryShares => 0x48
  | .units => 0x49
  | .miscliquidTrust => 0x4D
  | .ordinaryShares => 0x4F
  | .preferredStock => 0x50
  | .rights => 0x52
  | .sharesOfBeneficiaryInterest => 0x53
  | .test => 0x54
  | .units_55 => 0x55
  | .warrant => 0x57
  | .index => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x41 then .adr
  else if byte = 0x43 then .commonStock
  else if byte = 0x44 then .debentures
  else if byte = 0x45 then .etf
  else if byte = 0x46 then .foreign
  else if byte = 0x48 then .americanDepositoryShares
  else if byte = 0x49 then .units
  else if byte = 0x4D then .miscliquidTrust
  else if byte = 0x4F then .ordinaryShares
  else if byte = 0x50 then .preferredStock
  else if byte = 0x52 then .rights
  else if byte = 0x53 then .sharesOfBeneficiaryInterest
  else if byte = 0x54 then .test
  else if byte = 0x55 then .units_55
  else if byte = 0x57 then .warrant
  else .index

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | adr => decide
  | commonStock => decide
  | debentures => decide
  | etf => decide
  | foreign => decide
  | americanDepositoryShares => decide
  | units => decide
  | miscliquidTrust => decide
  | ordinaryShares => decide
  | preferredStock => decide
  | rights => decide
  | sharesOfBeneficiaryInterest => decide
  | test => decide
  | units_55 => decide
  | warrant => decide
  | index => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityType

/-- Send Time: 8 bytes -/
structure SendTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace SendTime

def encode (message : SendTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (SendTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : SendTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SendTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SendTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SendTime

/-- Outright Market Depth Buy Message: 44 bytes -/
structure OutrightMarketDepthBuyMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  firstLevelPrice : BitVec 32
  secondLevelPrice : BitVec 32
  thirdLevelPrice : BitVec 32
  firstLevelVolume : BitVec 16
  secondLevelVolume : BitVec 16
  thirdLevelVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  firstLevelCustomerVolume : BitVec 16
  secondLevelCustomerVolume : BitVec 16
  thirdLevelCustomerVolume : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightMarketDepthBuyMessage

def encode (message : OutrightMarketDepthBuyMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.firstLevelPrice
    ++ (encodeUIntLE 4 message.secondLevelPrice
    ++ (encodeUIntLE 4 message.thirdLevelPrice
    ++ (encodeUIntLE 2 message.firstLevelVolume
    ++ (encodeUIntLE 2 message.secondLevelVolume
    ++ (encodeUIntLE 2 message.thirdLevelVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.firstLevelCustomerVolume
    ++ (encodeUIntLE 2 message.secondLevelCustomerVolume
    ++ (encodeUIntLE 2 message.thirdLevelCustomerVolume
    ++ (Alpha.encode message.reserved2)))))))))))))))

def decode (bytes : List UInt8) : Option (OutrightMarketDepthBuyMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firstLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (secondLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (thirdLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (firstLevelVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondLevelVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdLevelVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (firstLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceNs, seriesIndex, symbolSeqNum, firstLevelPrice, secondLevelPrice, thirdLevelPrice, firstLevelVolume, secondLevelVolume, thirdLevelVolume, quoteCondition, reserved1, firstLevelCustomerVolume, secondLevelCustomerVolume, thirdLevelCustomerVolume, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightMarketDepthBuyMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightMarketDepthBuyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightMarketDepthBuyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightMarketDepthBuyMessage

/-- Outright Market Depth Sell Message: 44 bytes -/
structure OutrightMarketDepthSellMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  firstLevelPrice : BitVec 32
  secondLevelPrice : BitVec 32
  thirdLevelPrice : BitVec 32
  firstVolume : BitVec 16
  secondVolume : BitVec 16
  thirdVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  firstLevelCustomerVolume : BitVec 16
  secondLevelCustomerVolume : BitVec 16
  thirdLevelCustomerVolume : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightMarketDepthSellMessage

def encode (message : OutrightMarketDepthSellMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.firstLevelPrice
    ++ (encodeUIntLE 4 message.secondLevelPrice
    ++ (encodeUIntLE 4 message.thirdLevelPrice
    ++ (encodeUIntLE 2 message.firstVolume
    ++ (encodeUIntLE 2 message.secondVolume
    ++ (encodeUIntLE 2 message.thirdVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.firstLevelCustomerVolume
    ++ (encodeUIntLE 2 message.secondLevelCustomerVolume
    ++ (encodeUIntLE 2 message.thirdLevelCustomerVolume
    ++ (Alpha.encode message.reserved2)))))))))))))))

def decode (bytes : List UInt8) : Option (OutrightMarketDepthSellMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firstLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (secondLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (thirdLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (firstVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (firstLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceNs, seriesIndex, symbolSeqNum, firstLevelPrice, secondLevelPrice, thirdLevelPrice, firstVolume, secondVolume, thirdVolume, quoteCondition, reserved1, firstLevelCustomerVolume, secondLevelCustomerVolume, thirdLevelCustomerVolume, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightMarketDepthSellMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightMarketDepthSellMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightMarketDepthSellMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightMarketDepthSellMessage

/-- Underlying Status Message: 20 bytes -/
structure UnderlyingStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  underlyingIndex : BitVec 32
  underlyingSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UnderlyingStatusMessage

def encode (message : UnderlyingStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.underlyingIndex
    ++ (encodeUIntLE 4 message.underlyingSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (Alpha.encode message.haltCondition
    ++ (Alpha.encode message.reserved2))))))

def decode (bytes : List UInt8) : Option (UnderlyingStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, underlyingIndex, underlyingSeqNum, securityStatus, haltCondition, reserved2 }, bytes)

@[simp] theorem encode_length (message : UnderlyingStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingStatusMessage

/-- Outright Series Status Message: 20 bytes -/
structure OutrightSeriesStatusMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  securityStatus : SecurityStatus
  haltCondition : Alpha 1
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OutrightSeriesStatusMessage

def encode (message : OutrightSeriesStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (SecurityStatus.encode message.securityStatus
    ++ (Alpha.encode message.haltCondition
    ++ (Alpha.encode message.reserved2))))))

def decode (bytes : List UInt8) : Option (OutrightSeriesStatusMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltCondition, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, securityStatus, haltCondition, reserved2 }, bytes)

@[simp] theorem encode_length (message : OutrightSeriesStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SecurityStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OutrightSeriesStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightSeriesStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutrightSeriesStatusMessage

/-- Refresh Outright Market Depth Buy Message: 44 bytes -/
structure RefreshOutrightMarketDepthBuyMessage where
  sourceTime : BitVec 32
  sourceNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  firstLevelPrice : BitVec 32
  secondLevelPrice : BitVec 32
  thirdLevelPrice : BitVec 32
  firstVolume : BitVec 16
  secondVolume : BitVec 16
  thirdVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  firstLevelCustomerVolume : BitVec 16
  secondLevelCustomerVolume : BitVec 16
  thirdLevelCustomerVolume : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace RefreshOutrightMarketDepthBuyMessage

def encode (message : RefreshOutrightMarketDepthBuyMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.firstLevelPrice
    ++ (encodeUIntLE 4 message.secondLevelPrice
    ++ (encodeUIntLE 4 message.thirdLevelPrice
    ++ (encodeUIntLE 2 message.firstVolume
    ++ (encodeUIntLE 2 message.secondVolume
    ++ (encodeUIntLE 2 message.thirdVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.firstLevelCustomerVolume
    ++ (encodeUIntLE 2 message.secondLevelCustomerVolume
    ++ (encodeUIntLE 2 message.thirdLevelCustomerVolume
    ++ (Alpha.encode message.reserved2)))))))))))))))

def decode (bytes : List UInt8) : Option (RefreshOutrightMarketDepthBuyMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firstLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (secondLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (thirdLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (firstVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (firstLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceNs, seriesIndex, symbolSeqNum, firstLevelPrice, secondLevelPrice, thirdLevelPrice, firstVolume, secondVolume, thirdVolume, quoteCondition, reserved1, firstLevelCustomerVolume, secondLevelCustomerVolume, thirdLevelCustomerVolume, reserved2 }, bytes)

@[simp] theorem encode_length (message : RefreshOutrightMarketDepthBuyMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshOutrightMarketDepthBuyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshOutrightMarketDepthBuyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshOutrightMarketDepthBuyMessage

/-- Refresh Outright Market Depth Sell Message: 44 bytes -/
structure RefreshOutrightMarketDepthSellMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  seriesIndex : BitVec 32
  symbolSeqNum : BitVec 32
  firstLevelPrice : BitVec 32
  secondLevelPrice : BitVec 32
  thirdLevelPrice : BitVec 32
  firstVolume : BitVec 16
  secondVolume : BitVec 16
  thirdVolume : BitVec 16
  quoteCondition : QuoteCondition
  reserved1 : Alpha 1
  firstLevelCustomerVolume : BitVec 16
  secondLevelCustomerVolume : BitVec 16
  thirdLevelCustomerVolume : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace RefreshOutrightMarketDepthSellMessage

def encode (message : RefreshOutrightMarketDepthSellMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 4 message.symbolSeqNum
    ++ (encodeUIntLE 4 message.firstLevelPrice
    ++ (encodeUIntLE 4 message.secondLevelPrice
    ++ (encodeUIntLE 4 message.thirdLevelPrice
    ++ (encodeUIntLE 2 message.firstVolume
    ++ (encodeUIntLE 2 message.secondVolume
    ++ (encodeUIntLE 2 message.thirdVolume
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 2 message.firstLevelCustomerVolume
    ++ (encodeUIntLE 2 message.secondLevelCustomerVolume
    ++ (encodeUIntLE 2 message.thirdLevelCustomerVolume
    ++ (Alpha.encode message.reserved2)))))))))))))))

def decode (bytes : List UInt8) : Option (RefreshOutrightMarketDepthSellMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (symbolSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (firstLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (secondLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (thirdLevelPrice, bytes) ← decodeUIntLE 4 bytes
  let (firstVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdVolume, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (firstLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (secondLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (thirdLevelCustomerVolume, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceTime, sourceTimeNs, seriesIndex, symbolSeqNum, firstLevelPrice, secondLevelPrice, thirdLevelPrice, firstVolume, secondVolume, thirdVolume, quoteCondition, reserved1, firstLevelCustomerVolume, secondLevelCustomerVolume, thirdLevelCustomerVolume, reserved2 }, bytes)

@[simp] theorem encode_length (message : RefreshOutrightMarketDepthSellMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshOutrightMarketDepthSellMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshOutrightMarketDepthSellMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshOutrightMarketDepthSellMessage

/-- Underlying Index Mapping Message: 24 bytes -/
structure UnderlyingIndexMappingMessage where
  underlyingIndex : BitVec 32
  underlyingSymbol : Alpha 11
  channelId : BitVec 8
  marketId : BitVec 16
  systemId : BitVec 8
  exchangeCode : ExchangeCode
  priceScaleCode : BitVec 8
  securityType : SecurityType
  priceResolution : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace UnderlyingIndexMappingMessage

def encode (message : UnderlyingIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.underlyingIndex
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 1 message.channelId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (SecurityType.encode message.securityType
    ++ (encodeUIntLE 1 message.priceResolution
    ++ (Alpha.encode message.reserved1)))))))))

def decode (bytes : List UInt8) : Option (UnderlyingIndexMappingMessage × List UInt8) := do
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (priceResolution, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ underlyingIndex, underlyingSymbol, channelId, marketId, systemId, exchangeCode, priceScaleCode, securityType, priceResolution, reserved1 }, bytes)

@[simp] theorem encode_length (message : UnderlyingIndexMappingMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ExchangeCode.encode_length, SecurityType.encode_length]

theorem encode_length_pos (message : UnderlyingIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingIndexMappingMessage

/-- Series Index Mapping Message: 56 bytes -/
structure SeriesIndexMappingMessage where
  seriesIndex : BitVec 32
  channelId : BitVec 8
  reservedA1 : Alpha 1
  marketId : BitVec 16
  systemId : BitVec 8
  reservedB1 : Alpha 1
  streamId : BitVec 16
  underlyingIndex : BitVec 32
  contractMultiplier : BitVec 16
  maturityDate : Alpha 6
  putOrCall : BitVec 8
  strikePrice : Alpha 10
  priceScaleCode : BitVec 8
  underlyingSymbol : Alpha 11
  optionSymbolRoot : Alpha 5
  groupId : BitVec 32
  deriving DecidableEq, Repr

namespace SeriesIndexMappingMessage

def encode (message : SeriesIndexMappingMessage) : List UInt8 :=
  encodeUIntLE 4 message.seriesIndex
    ++ (encodeUIntLE 1 message.channelId
    ++ (Alpha.encode message.reservedA1
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 1 message.systemId
    ++ (Alpha.encode message.reservedB1
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 4 message.underlyingIndex
    ++ (encodeUIntLE 2 message.contractMultiplier
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUIntLE 1 message.putOrCall
    ++ (Alpha.encode message.strikePrice
    ++ (encodeUIntLE 1 message.priceScaleCode
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.optionSymbolRoot
    ++ (encodeUIntLE 4 message.groupId)))))))))))))))

def decode (bytes : List UInt8) : Option (SeriesIndexMappingMessage × List UInt8) := do
  let (seriesIndex, bytes) ← decodeUIntLE 4 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  let (reservedA1, bytes) ← Alpha.decode 1 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (systemId, bytes) ← decodeUIntLE 1 bytes
  let (reservedB1, bytes) ← Alpha.decode 1 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (underlyingIndex, bytes) ← decodeUIntLE 4 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (maturityDate, bytes) ← Alpha.decode 6 bytes
  let (putOrCall, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← Alpha.decode 10 bytes
  let (priceScaleCode, bytes) ← decodeUIntLE 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (optionSymbolRoot, bytes) ← Alpha.decode 5 bytes
  let (groupId, bytes) ← decodeUIntLE 4 bytes
  pure ({ seriesIndex, channelId, reservedA1, marketId, systemId, reservedB1, streamId, underlyingIndex, contractMultiplier, maturityDate, putOrCall, strikePrice, priceScaleCode, underlyingSymbol, optionSymbolRoot, groupId }, bytes)

@[simp] theorem encode_length (message : SeriesIndexMappingMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesIndexMappingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesIndexMappingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SeriesIndexMappingMessage

/-- Stream Id Message: 4 bytes -/
structure StreamIdMessage where
  streamId : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace StreamIdMessage

def encode (message : StreamIdMessage) : List UInt8 :=
  encodeUIntLE 2 message.streamId
    ++ (Alpha.encode message.reserved2)

def decode (bytes : List UInt8) : Option (StreamIdMessage × List UInt8) := do
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ streamId, reserved2 }, bytes)

@[simp] theorem encode_length (message : StreamIdMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StreamIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StreamIdMessage

/-- Sequence Number Reset Message: 10 bytes -/
structure SequenceNumberResetMessage where
  sourceTime : BitVec 32
  sourceTimeNs : BitVec 32
  productId : BitVec 8
  channelId : BitVec 8
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.sourceTime
    ++ (encodeUIntLE 4 message.sourceTimeNs
    ++ (encodeUIntLE 1 message.productId
    ++ (encodeUIntLE 1 message.channelId)))

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUIntLE 4 bytes
  let (sourceTimeNs, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 1 bytes
  let (channelId, bytes) ← decodeUIntLE 1 bytes
  pure ({ sourceTime, sourceTimeNs, productId, channelId }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceNumberResetMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | outrightMarketDepthBuyMessage (message : OutrightMarketDepthBuyMessage) -- 403
  | outrightMarketDepthSellMessage (message : OutrightMarketDepthSellMessage) -- 405
  | underlyingStatusMessage (message : UnderlyingStatusMessage) -- 419
  | outrightSeriesStatusMessage (message : OutrightSeriesStatusMessage) -- 421
  | refreshOutrightMarketDepthBuyMessage (message : RefreshOutrightMarketDepthBuyMessage) -- 503
  | refreshOutrightMarketDepthSellMessage (message : RefreshOutrightMarketDepthSellMessage) -- 505
  | underlyingIndexMappingMessage (message : UnderlyingIndexMappingMessage) -- 435
  | seriesIndexMappingMessage (message : SeriesIndexMappingMessage) -- 437
  | streamIdMessage (message : StreamIdMessage) -- 455
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 1
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .outrightMarketDepthBuyMessage _ => 403
  | .outrightMarketDepthSellMessage _ => 405
  | .underlyingStatusMessage _ => 419
  | .outrightSeriesStatusMessage _ => 421
  | .refreshOutrightMarketDepthBuyMessage _ => 503
  | .refreshOutrightMarketDepthSellMessage _ => 505
  | .underlyingIndexMappingMessage _ => 435
  | .seriesIndexMappingMessage _ => 437
  | .streamIdMessage _ => 455
  | .sequenceNumberResetMessage _ => 1

def encode : Payload → List UInt8
  | .outrightMarketDepthBuyMessage message => OutrightMarketDepthBuyMessage.encode message
  | .outrightMarketDepthSellMessage message => OutrightMarketDepthSellMessage.encode message
  | .underlyingStatusMessage message => UnderlyingStatusMessage.encode message
  | .outrightSeriesStatusMessage message => OutrightSeriesStatusMessage.encode message
  | .refreshOutrightMarketDepthBuyMessage message => RefreshOutrightMarketDepthBuyMessage.encode message
  | .refreshOutrightMarketDepthSellMessage message => RefreshOutrightMarketDepthSellMessage.encode message
  | .underlyingIndexMappingMessage message => UnderlyingIndexMappingMessage.encode message
  | .seriesIndexMappingMessage message => SeriesIndexMappingMessage.encode message
  | .streamIdMessage message => StreamIdMessage.encode message
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 56 := by
  cases message with
  | outrightMarketDepthBuyMessage inner =>
    simp only [encode, OutrightMarketDepthBuyMessage.encode_length]
    omega
  | outrightMarketDepthSellMessage inner =>
    simp only [encode, OutrightMarketDepthSellMessage.encode_length]
    omega
  | underlyingStatusMessage inner =>
    simp only [encode, UnderlyingStatusMessage.encode_length]
    omega
  | outrightSeriesStatusMessage inner =>
    simp only [encode, OutrightSeriesStatusMessage.encode_length]
    omega
  | refreshOutrightMarketDepthBuyMessage inner =>
    simp only [encode, RefreshOutrightMarketDepthBuyMessage.encode_length]
    omega
  | refreshOutrightMarketDepthSellMessage inner =>
    simp only [encode, RefreshOutrightMarketDepthSellMessage.encode_length]
    omega
  | underlyingIndexMappingMessage inner =>
    simp only [encode, UnderlyingIndexMappingMessage.encode_length]
    omega
  | seriesIndexMappingMessage inner =>
    simp only [encode, SeriesIndexMappingMessage.encode_length]
    omega
  | streamIdMessage inner =>
    simp only [encode, StreamIdMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 403 then (OutrightMarketDepthBuyMessage.decode bytes).map fun (message, rest) => (.outrightMarketDepthBuyMessage message, rest)
  else if tag = 405 then (OutrightMarketDepthSellMessage.decode bytes).map fun (message, rest) => (.outrightMarketDepthSellMessage message, rest)
  else if tag = 419 then (UnderlyingStatusMessage.decode bytes).map fun (message, rest) => (.underlyingStatusMessage message, rest)
  else if tag = 421 then (OutrightSeriesStatusMessage.decode bytes).map fun (message, rest) => (.outrightSeriesStatusMessage message, rest)
  else if tag = 503 then (RefreshOutrightMarketDepthBuyMessage.decode bytes).map fun (message, rest) => (.refreshOutrightMarketDepthBuyMessage message, rest)
  else if tag = 505 then (RefreshOutrightMarketDepthSellMessage.decode bytes).map fun (message, rest) => (.refreshOutrightMarketDepthSellMessage message, rest)
  else if tag = 435 then (UnderlyingIndexMappingMessage.decode bytes).map fun (message, rest) => (.underlyingIndexMappingMessage message, rest)
  else if tag = 437 then (SeriesIndexMappingMessage.decode bytes).map fun (message, rest) => (.seriesIndexMappingMessage message, rest)
  else if tag = 455 then (StreamIdMessage.decode bytes).map fun (message, rest) => (.streamIdMessage message, rest)
  else if tag = 1 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | outrightMarketDepthBuyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightMarketDepthBuyMessage.encode_length]
    omega
  | outrightMarketDepthSellMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightMarketDepthSellMessage.encode_length]
    omega
  | underlyingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, UnderlyingStatusMessage.encode_length]
    omega
  | outrightSeriesStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OutrightSeriesStatusMessage.encode_length]
    omega
  | refreshOutrightMarketDepthBuyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshOutrightMarketDepthBuyMessage.encode_length]
    omega
  | refreshOutrightMarketDepthSellMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshOutrightMarketDepthSellMessage.encode_length]
    omega
  | underlyingIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, UnderlyingIndexMappingMessage.encode_length]
    omega
  | seriesIndexMappingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SeriesIndexMappingMessage.encode_length]
    omega
  | streamIdMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, StreamIdMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SequenceNumberResetMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetSize : BitVec 16
  deliveryFlag : BitVec 8
  sequenceNumber : BitVec 32
  sendTime : SendTime
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.packetSize
    ++ (encodeUIntLE 1 message.deliveryFlag
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (SendTime.encode message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUIntLE 2 bytes
  let (deliveryFlag, bytes) ← decodeUIntLE 1 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← SendTime.decode bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, deliveryFlag, sequenceNumber, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SendTime.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NyseArcaoptionsDeepfeedXdpV13A
