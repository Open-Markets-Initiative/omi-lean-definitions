import Wire

/-!
# OTC Markets Group OTC Top of Book v1.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.OtcmarketsLinknqbTopofbookLinkV118

/-- Reporting Status: one byte code -/
def ReportingStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x46, 0x47, 0x49, 0x4E, 0x4F, 0x52, 0x56, 0x57]

inductive ReportingStatus where
  | alternativeReportingStandard -- Alternative Reporting Standard
  | bankThrift -- Bank Thrift
  | secReporting -- Sec Reporting
  | internationalReporting -- International Reporting
  | insuranceCompany -- Insurance Company
  | noReporting -- No Reporting
  | otherReportingStandard -- Other Reporting Standard
  | finraReporting -- Finra Reporting
  | secReportingInvestmentCompany -- Sec Reporting Investment Company
  | secReportingRegA -- Sec Reporting Reg A
  | unlisted (byte : { byte : UInt8 // byte ∉ ReportingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReportingStatus

def toByte : ReportingStatus → UInt8
  | .alternativeReportingStandard => 0x41
  | .bankThrift => 0x42
  | .secReporting => 0x46
  | .internationalReporting => 0x47
  | .insuranceCompany => 0x49
  | .noReporting => 0x4E
  | .otherReportingStandard => 0x4F
  | .finraReporting => 0x52
  | .secReportingInvestmentCompany => 0x56
  | .secReportingRegA => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReportingStatus :=
  if byte = 0x41 then .alternativeReportingStandard
  else if byte = 0x42 then .bankThrift
  else if byte = 0x46 then .secReporting
  else if byte = 0x47 then .internationalReporting
  else if byte = 0x49 then .insuranceCompany
  else if byte = 0x4E then .noReporting
  else if byte = 0x4F then .otherReportingStandard
  else if byte = 0x52 then .finraReporting
  else if byte = 0x56 then .secReportingInvestmentCompany
  else .secReportingRegA

def ofByte (byte : UInt8) : ReportingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReportingStatus) : ofByte value.toByte = value := by
  cases value with
  | alternativeReportingStandard => decide
  | bankThrift => decide
  | secReporting => decide
  | internationalReporting => decide
  | insuranceCompany => decide
  | noReporting => decide
  | otherReportingStandard => decide
  | finraReporting => decide
  | secReportingInvestmentCompany => decide
  | secReportingRegA => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReportingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReportingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReportingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReportingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReportingStatus

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x41, 0x51, 0x53, 0x48, 0x49, 0x52, 0x44, 0x58]

inductive SecurityStatus where
  | active -- Active
  | quoteOnly -- Quote Only
  | suspended -- Suspended
  | halted -- Halted
  | internalHalt -- Internal Halt
  | revoked -- Revoked
  | deleted -- Deleted
  | removedFromIdqs -- Removed From Idqs
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .active => 0x41
  | .quoteOnly => 0x51
  | .suspended => 0x53
  | .halted => 0x48
  | .internalHalt => 0x49
  | .revoked => 0x52
  | .deleted => 0x44
  | .removedFromIdqs => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x41 then .active
  else if byte = 0x51 then .quoteOnly
  else if byte = 0x53 then .suspended
  else if byte = 0x48 then .halted
  else if byte = 0x49 then .internalHalt
  else if byte = 0x52 then .revoked
  else if byte = 0x44 then .deleted
  else .removedFromIdqs

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | quoteOnly => decide
  | suspended => decide
  | halted => decide
  | internalHalt => decide
  | revoked => decide
  | deleted => decide
  | removedFromIdqs => decide
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

/-- Unsolicited: one byte code -/
def Unsolicited.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Unsolicited where
  | unsolicited -- Unsolicited
  | notUnsolicited -- Not Unsolicited
  | unlisted (byte : { byte : UInt8 // byte ∉ Unsolicited.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Unsolicited

def toByte : Unsolicited → UInt8
  | .unsolicited => 0x59
  | .notUnsolicited => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Unsolicited :=
  if byte = 0x59 then .unsolicited
  else .notUnsolicited

def ofByte (byte : UInt8) : Unsolicited :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Unsolicited) : ofByte value.toByte = value := by
  cases value with
  | unsolicited => decide
  | notUnsolicited => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Unsolicited) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Unsolicited × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Unsolicited) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Unsolicited) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Unsolicited

/-- Current Inside Imbalance Side: one byte code -/
def CurrentInsideImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x4E, 0x4F]

inductive CurrentInsideImbalanceSide where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | noImbalance -- No Imbalance
  | noMarketableOrders -- No Marketable Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentInsideImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentInsideImbalanceSide

def toByte : CurrentInsideImbalanceSide → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .noImbalance => 0x4E
  | .noMarketableOrders => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentInsideImbalanceSide :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else if byte = 0x4E then .noImbalance
  else .noMarketableOrders

def ofByte (byte : UInt8) : CurrentInsideImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentInsideImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | noImbalance => decide
  | noMarketableOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentInsideImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentInsideImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentInsideImbalanceSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CurrentInsideImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentInsideImbalanceSide

/-- Moc Shares Unmatched: one byte code -/
def MocSharesUnmatched.codes : List UInt8 :=
  [0x42, 0x53, 0x4F]

inductive MocSharesUnmatched where
  | buyMocNotMatched -- Buy Moc Not Matched
  | sellMocNotMatched -- Sell Moc Not Matched
  | noMocUnmatched -- No Moc Unmatched
  | unlisted (byte : { byte : UInt8 // byte ∉ MocSharesUnmatched.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MocSharesUnmatched

def toByte : MocSharesUnmatched → UInt8
  | .buyMocNotMatched => 0x42
  | .sellMocNotMatched => 0x53
  | .noMocUnmatched => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MocSharesUnmatched :=
  if byte = 0x42 then .buyMocNotMatched
  else if byte = 0x53 then .sellMocNotMatched
  else .noMocUnmatched

def ofByte (byte : UInt8) : MocSharesUnmatched :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MocSharesUnmatched) : ofByte value.toByte = value := by
  cases value with
  | buyMocNotMatched => decide
  | sellMocNotMatched => decide
  | noMocUnmatched => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MocSharesUnmatched) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MocSharesUnmatched × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MocSharesUnmatched) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MocSharesUnmatched) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MocSharesUnmatched

/-- Start Of Spin Message: 13 bytes -/
structure StartOfSpinMessage where
  spinType : BitVec 8
  spinStartTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace StartOfSpinMessage

def encode (message : StartOfSpinMessage) : List UInt8 :=
  encodeUInt 1 message.spinType
    ++ (encodeUInt 8 message.spinStartTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum))

def decode (bytes : List UInt8) : Option (StartOfSpinMessage × List UInt8) := do
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinStartTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ spinType, spinStartTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : StartOfSpinMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StartOfSpinMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSpinMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfSpinMessage

/-- End Of Spin Message: 17 bytes -/
structure EndOfSpinMessage where
  spinType : BitVec 8
  spinMsgCt : BitVec 32
  spinEndTimeMilli : BitVec 64
  spinLastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfSpinMessage

def encode (message : EndOfSpinMessage) : List UInt8 :=
  encodeUInt 1 message.spinType
    ++ (encodeUInt 4 message.spinMsgCt
    ++ (encodeUInt 8 message.spinEndTimeMilli
    ++ (encodeUInt 4 message.spinLastSeqNum)))

def decode (bytes : List UInt8) : Option (EndOfSpinMessage × List UInt8) := do
  let (spinType, bytes) ← decodeUInt 1 bytes
  let (spinMsgCt, bytes) ← decodeUInt 4 bytes
  let (spinEndTimeMilli, bytes) ← decodeUInt 8 bytes
  let (spinLastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ spinType, spinMsgCt, spinEndTimeMilli, spinLastSeqNum }, bytes)

@[simp] theorem encode_length (message : EndOfSpinMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EndOfSpinMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSpinMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndOfSpinMessage

/-- Trading Session Message: 9 bytes -/
structure TradingSessionMessage where
  sessionTime : BitVec 64
  tradingSession : BitVec 8
  deriving DecidableEq, Repr

namespace TradingSessionMessage

def encode (message : TradingSessionMessage) : List UInt8 :=
  encodeUInt 8 message.sessionTime
    ++ (encodeUInt 1 message.tradingSession)

def decode (bytes : List UInt8) : Option (TradingSessionMessage × List UInt8) := do
  let (sessionTime, bytes) ← decodeUInt 8 bytes
  let (tradingSession, bytes) ← decodeUInt 1 bytes
  pure ({ sessionTime, tradingSession }, bytes)

@[simp] theorem encode_length (message : TradingSessionMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradingSessionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingSessionMessage

/-- Security Message: 33 bytes -/
structure SecurityMessage where
  symbol : Alpha 14
  lastUpdateMilli : BitVec 64
  securityAction : BitVec 8
  assetClass : BitVec 8
  securityId : BitVec 32
  securityFlags : BitVec 16
  tier : BitVec 8
  reportingStatus : ReportingStatus
  securityStatus : SecurityStatus
  deriving DecidableEq, Repr

namespace SecurityMessage

def encode (message : SecurityMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUInt 8 message.lastUpdateMilli
    ++ (encodeUInt 1 message.securityAction
    ++ (encodeUInt 1 message.assetClass
    ++ (encodeUInt 4 message.securityId
    ++ (encodeUInt 2 message.securityFlags
    ++ (encodeUInt 1 message.tier
    ++ (ReportingStatus.encode message.reportingStatus
    ++ (SecurityStatus.encode message.securityStatus))))))))

def decode (bytes : List UInt8) : Option (SecurityMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (lastUpdateMilli, bytes) ← decodeUInt 8 bytes
  let (securityAction, bytes) ← decodeUInt 1 bytes
  let (assetClass, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUInt 4 bytes
  let (securityFlags, bytes) ← decodeUInt 2 bytes
  let (tier, bytes) ← decodeUInt 1 bytes
  let (reportingStatus, bytes) ← ReportingStatus.decode bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  pure ({ symbol, lastUpdateMilli, securityAction, assetClass, securityId, securityFlags, tier, reportingStatus, securityStatus }, bytes)

@[simp] theorem encode_length (message : SecurityMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ReportingStatus.encode_length, SecurityStatus.encode_length]

theorem encode_length_pos (message : SecurityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ReportingStatus.decode_encode, some_bind]
  dsimp only
  rw [SecurityStatus.decode_encode, some_bind]
  rfl

end SecurityMessage

/-- Top Of Book Message: 43 bytes -/
structure TopOfBookMessage where
  time : BitVec 32
  symbol : Alpha 14
  askPrice : BitVec 64
  askVolume : BitVec 32
  bidPrice : BitVec 64
  bidVolume : BitVec 32
  unsolicited : Unsolicited
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.askPrice
    ++ (encodeUInt 4 message.askVolume
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidVolume
    ++ (Unsolicited.encode message.unsolicited))))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (askPrice, bytes) ← decodeUInt 8 bytes
  let (askVolume, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidVolume, bytes) ← decodeUInt 4 bytes
  let (unsolicited_, bytes) ← Unsolicited.decode bytes
  pure ({ time, symbol, askPrice, askVolume, bidPrice, bidVolume, unsolicited := unsolicited_ }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Unsolicited.encode_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Unsolicited.decode_encode, some_bind]
  rfl

end TopOfBookMessage

/-- Imbalance Message: 52 bytes -/
structure ImbalanceMessage where
  time : BitVec 32
  symbol : Alpha 14
  currentInsidePairedShares : BitVec 32
  currentInsideClosingPrice : BitVec 64
  currentInsideImbalanceQuantity : BitVec 32
  currentInsideImbalanceSide : CurrentInsideImbalanceSide
  fullClosingPrice : BitVec 64
  ocioOnlyClosingPrice : BitVec 64
  mocSharesUnmatched : MocSharesUnmatched
  deriving DecidableEq, Repr

namespace ImbalanceMessage

def encode (message : ImbalanceMessage) : List UInt8 :=
  encodeUInt 4 message.time
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.currentInsidePairedShares
    ++ (encodeUInt 8 message.currentInsideClosingPrice
    ++ (encodeUInt 4 message.currentInsideImbalanceQuantity
    ++ (CurrentInsideImbalanceSide.encode message.currentInsideImbalanceSide
    ++ (encodeUInt 8 message.fullClosingPrice
    ++ (encodeUInt 8 message.ocioOnlyClosingPrice
    ++ (MocSharesUnmatched.encode message.mocSharesUnmatched))))))))

def decode (bytes : List UInt8) : Option (ImbalanceMessage × List UInt8) := do
  let (time, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 14 bytes
  let (currentInsidePairedShares, bytes) ← decodeUInt 4 bytes
  let (currentInsideClosingPrice, bytes) ← decodeUInt 8 bytes
  let (currentInsideImbalanceQuantity, bytes) ← decodeUInt 4 bytes
  let (currentInsideImbalanceSide, bytes) ← CurrentInsideImbalanceSide.decode bytes
  let (fullClosingPrice, bytes) ← decodeUInt 8 bytes
  let (ocioOnlyClosingPrice, bytes) ← decodeUInt 8 bytes
  let (mocSharesUnmatched, bytes) ← MocSharesUnmatched.decode bytes
  pure ({ time, symbol, currentInsidePairedShares, currentInsideClosingPrice, currentInsideImbalanceQuantity, currentInsideImbalanceSide, fullClosingPrice, ocioOnlyClosingPrice, mocSharesUnmatched }, bytes)

@[simp] theorem encode_length (message : ImbalanceMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CurrentInsideImbalanceSide.encode_length, MocSharesUnmatched.encode_length]

theorem encode_length_pos (message : ImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImbalanceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentInsideImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MocSharesUnmatched.decode_encode, some_bind]
  rfl

end ImbalanceMessage

/-- System Recovery Event Message: 17 bytes -/
structure SystemRecoveryEventMessage where
  deprecated : BitVec 32
  recoveryType : BitVec 8
  nextSequenceNumber : BitVec 32
  recoveryStartTime : BitVec 64
  deriving DecidableEq, Repr

namespace SystemRecoveryEventMessage

def encode (message : SystemRecoveryEventMessage) : List UInt8 :=
  encodeUInt 4 message.deprecated
    ++ (encodeUInt 1 message.recoveryType
    ++ (encodeUInt 4 message.nextSequenceNumber
    ++ (encodeUInt 8 message.recoveryStartTime)))

def decode (bytes : List UInt8) : Option (SystemRecoveryEventMessage × List UInt8) := do
  let (deprecated, bytes) ← decodeUInt 4 bytes
  let (recoveryType, bytes) ← decodeUInt 1 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (recoveryStartTime, bytes) ← decodeUInt 8 bytes
  pure ({ deprecated, recoveryType, nextSequenceNumber, recoveryStartTime }, bytes)

@[simp] theorem encode_length (message : SystemRecoveryEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SystemRecoveryEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemRecoveryEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemRecoveryEventMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | startOfSpinMessage (message : StartOfSpinMessage) -- 11
  | endOfSpinMessage (message : EndOfSpinMessage) -- 12
  | tradingSessionMessage (message : TradingSessionMessage) -- 20
  | securityMessage (message : SecurityMessage) -- 9
  | topOfBookMessage (message : TopOfBookMessage) -- 27
  | imbalanceMessage (message : ImbalanceMessage) -- 28
  | systemRecoveryEventMessage (message : SystemRecoveryEventMessage) -- 74
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .startOfSpinMessage _ => 11
  | .endOfSpinMessage _ => 12
  | .tradingSessionMessage _ => 20
  | .securityMessage _ => 9
  | .topOfBookMessage _ => 27
  | .imbalanceMessage _ => 28
  | .systemRecoveryEventMessage _ => 74

def encode : Payload → List UInt8
  | .startOfSpinMessage message => StartOfSpinMessage.encode message
  | .endOfSpinMessage message => EndOfSpinMessage.encode message
  | .tradingSessionMessage message => TradingSessionMessage.encode message
  | .securityMessage message => SecurityMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message
  | .imbalanceMessage message => ImbalanceMessage.encode message
  | .systemRecoveryEventMessage message => SystemRecoveryEventMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 52 := by
  cases message with
  | startOfSpinMessage inner =>
    simp only [encode, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [encode, EndOfSpinMessage.encode_length]
    omega
  | tradingSessionMessage inner =>
    simp only [encode, TradingSessionMessage.encode_length]
    omega
  | securityMessage inner =>
    simp only [encode, SecurityMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [encode, ImbalanceMessage.encode_length]
    omega
  | systemRecoveryEventMessage inner =>
    simp only [encode, SystemRecoveryEventMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 11 then (StartOfSpinMessage.decode bytes).map fun (message, rest) => (.startOfSpinMessage message, rest)
  else if tag = 12 then (EndOfSpinMessage.decode bytes).map fun (message, rest) => (.endOfSpinMessage message, rest)
  else if tag = 20 then (TradingSessionMessage.decode bytes).map fun (message, rest) => (.tradingSessionMessage message, rest)
  else if tag = 9 then (SecurityMessage.decode bytes).map fun (message, rest) => (.securityMessage message, rest)
  else if tag = 27 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else if tag = 28 then (ImbalanceMessage.decode bytes).map fun (message, rest) => (.imbalanceMessage message, rest)
  else if tag = 74 then (SystemRecoveryEventMessage.decode bytes).map fun (message, rest) => (.systemRecoveryEventMessage message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | startOfSpinMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StartOfSpinMessage.encode_length]
    omega
  | endOfSpinMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfSpinMessage.encode_length]
    omega
  | tradingSessionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingSessionMessage.encode_length]
    omega
  | securityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopOfBookMessage.encode_length]
    omega
  | imbalanceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ImbalanceMessage.encode_length]
    omega
  | systemRecoveryEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemRecoveryEventMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetSize : BitVec 16
  seqNum : BitVec 32
  packetFlag : BitVec 8
  packetMilli : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetSize
    ++ (encodeUInt 4 message.seqNum
    ++ (encodeUIntLE 1 message.packetFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 4 message.packetMilli
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (packetSize, bytes) ← decodeUInt 2 bytes
  let (seqNum, bytes) ← decodeUInt 4 bytes
  let (packetFlag, bytes) ← decodeUIntLE 1 bytes
  let (messages, bytes) ← decodeUInt 1 bytes
  let (packetMilli, bytes) ← decodeUInt 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messages.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ packetSize, seqNum, packetFlag, packetMilli, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.OtcmarketsLinknqbTopofbookLinkV118
