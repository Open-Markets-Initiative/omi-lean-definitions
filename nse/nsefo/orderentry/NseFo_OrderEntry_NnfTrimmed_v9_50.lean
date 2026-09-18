import Omi.Wire

/-!
# National Stock Exchange of India Ltd Order Entry v9.50

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Additional Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Board Lot In Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Order Modify Cancel Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Order Modify Cancel Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Order Modify Cancel Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Order Modify Cancel Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Order Confirmation Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Order Confirmation Trimmed Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Quick Acknowledgement Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsefoOrderentryNnftrimmedV950

/-- Contract Desc Tr: 26 bytes -/
structure ContractDescTr where
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  deriving DecidableEq, Repr

namespace ContractDescTr

def encode (message : ContractDescTr) : List UInt8 :=
  Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType))))

def decode (bytes : List UInt8) : Option (ContractDescTr × List UInt8) := do
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  pure ({ instrumentName, symbol, expiryDate, strikePrice, optionType }, bytes)

@[simp] theorem encode_length (message : ContractDescTr) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ContractDescTr) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractDescTr) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ContractDescTr

/-- Board Lot In Trimmed Message: 156 bytes -/
structure BoardLotInTrimmedMessage where
  userId : BitVec 32
  reasonCode : BitVec 16
  tokenNo : BitVec 32
  contractDescTr : ContractDescTr
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  goodTillDate : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  filler : BitVec 32
  nnfField : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace BoardLotInTrimmedMessage

def encode (message : BoardLotInTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.filler
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.reserved32)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BoardLotInTrimmedMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ userId, reasonCode, tokenNo, contractDescTr, accountNumber, bookType, buySellIndicator, disclosedVolume, volume, price, goodTillDate, stOrderFlags, branchId, traderId, brokerId, openClose, settlor, proClientIndicator, additionalOrderFlags, reserved1, filler, nnfField, pan, algoId, reserved2, reserved32 }, bytes)

@[simp] theorem encode_length (message : BoardLotInTrimmedMessage) : (encode message).length = 156 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDescTr.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BoardLotInTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BoardLotInTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoardLotInTrimmedMessage

/-- Order Modify Cancel Trimmed Message: 184 bytes -/
structure OrderModifyCancelTrimmedMessage where
  userId : BitVec 32
  modifiedCancelledBy : Alpha 1
  reserved1 : Alpha 1
  tokenNo : BitVec 32
  contractDescTr : ContractDescTr
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  additionalOrderFlags : BitVec 8
  secondReserved1 : Alpha 1
  filler : BitVec 32
  nnfField : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace OrderModifyCancelTrimmedMessage

def encode (message : OrderModifyCancelTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.filler
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved24)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModifyCancelTrimmedMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ userId, modifiedCancelledBy, reserved1, tokenNo, contractDescTr, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, goodTillDate, entryDateTime, lastModified, stOrderFlags, branchId, traderId, brokerId, openClose, settlor, proClientIndicator, additionalOrderFlags, secondReserved1, filler, nnfField, pan, algoId, reserved2, lastActivityReference, reserved24 }, bytes)

@[simp] theorem encode_length (message : OrderModifyCancelTrimmedMessage) : (encode message).length = 184 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractDescTr.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyCancelTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModifyCancelTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModifyCancelTrimmedMessage

/-- Order Confirmation Trimmed Message: 238 bytes -/
structure OrderConfirmationTrimmedMessage where
  logTime : BitVec 32
  userId : BitVec 32
  errorCode : BitVec 16
  timestamp1LongLong : BitVec 64
  timestamp2Char : Alpha 1
  modifiedCancelledBy : Alpha 1
  reasonCode : BitVec 16
  tokenNo : BitVec 32
  contractDescTr : ContractDescTr
  closeoutFlag : Alpha 1
  reserved1 : Alpha 1
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  additionalOrderFlags : BitVec 8
  secondReserved1 : Alpha 1
  filler : BitVec 32
  nnfField : Alpha 8
  timeStamp : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderConfirmationTrimmedMessage

def encode (message : OrderConfirmationTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.timestamp1LongLong
    ++ (Alpha.encode message.timestamp2Char
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.filler
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderConfirmationTrimmedMessage × List UInt8) := do
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (timestamp1LongLong, bytes) ← decodeUInt 8 bytes
  let (timestamp2Char, bytes) ← Alpha.decode 1 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ logTime, userId, errorCode, timestamp1LongLong, timestamp2Char, modifiedCancelledBy, reasonCode, tokenNo, contractDescTr, closeoutFlag, reserved1, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, goodTillDate, entryDateTime, lastModified, stOrderFlags, branchId, traderId, brokerId, openClose, settlor, proClientIndicator, additionalOrderFlags, secondReserved1, filler, nnfField, timeStamp, pan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderConfirmationTrimmedMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractDescTr.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderConfirmationTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderConfirmationTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderConfirmationTrimmedMessage

/-- Trade Confirmation Trimmed Message: 228 bytes -/
structure TradeConfirmationTrimmedMessage where
  logTime : BitVec 32
  traderId : BitVec 32
  timeStamp : BitVec 64
  timestamp1Double : Alpha 8
  timestamp2Double : Alpha 8
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  token : BitVec 32
  contractDescTr : ContractDescTr
  openClose : Alpha 1
  tradeBookType : Alpha 1
  participant : Alpha 12
  additionalOrderFlags : BitVec 8
  pan : Alpha 10
  secondReserved1 : Alpha 1
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeConfirmationTrimmedMessage

def encode (message : TradeConfirmationTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.timestamp1Double
    ++ (Alpha.encode message.timestamp2Double
    ++ (Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (encodeUInt 4 message.token
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.participant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationTrimmedMessage × List UInt8) := do
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (timestamp1Double, bytes) ← Alpha.decode 8 bytes
  let (timestamp2Double, bytes) ← Alpha.decode 8 bytes
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ logTime, traderId, timeStamp, timestamp1Double, timestamp2Double, responseOrderNumber, brokerId, reserved1, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, token, contractDescTr, openClose, tradeBookType, participant, additionalOrderFlags, pan, secondReserved1, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationTrimmedMessage) : (encode message).length = 228 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractDescTr.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeConfirmationTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeConfirmationTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeConfirmationTrimmedMessage

/-- Quick Acknowledgement Message: 20 bytes -/
structure QuickAcknowledgementMessage where
  traderId : BitVec 32
  timeStamp : BitVec 64
  reference : BitVec 32
  errorCode : BitVec 16
  messageLength : BitVec 16
  deriving DecidableEq, Repr

namespace QuickAcknowledgementMessage

def encode (message : QuickAcknowledgementMessage) : List UInt8 :=
  encodeUInt 4 message.traderId
    ++ (encodeUInt 8 message.timeStamp
    ++ (encodeUInt 4 message.reference
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 2 message.messageLength))))

def decode (bytes : List UInt8) : Option (QuickAcknowledgementMessage × List UInt8) := do
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  pure ({ traderId, timeStamp, reference, errorCode, messageLength }, bytes)

@[simp] theorem encode_length (message : QuickAcknowledgementMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuickAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuickAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuickAcknowledgementMessage

/-- Any Message Payload, selected by Transaction Code -/
inductive MessagePayload where
  | boardLotInTrimmedMessage (message : BoardLotInTrimmedMessage) -- 20000
  | boardLotInTrimmedMessage20400 (message : BoardLotInTrimmedMessage) -- 20400
  | orderModifyCancelTrimmedMessage (message : OrderModifyCancelTrimmedMessage) -- 20040
  | orderModifyCancelTrimmedMessage20060 (message : OrderModifyCancelTrimmedMessage) -- 20060
  | orderModifyCancelTrimmedMessage20070 (message : OrderModifyCancelTrimmedMessage) -- 20070
  | orderModifyCancelTrimmedMessage20402 (message : OrderModifyCancelTrimmedMessage) -- 20402
  | orderModifyCancelTrimmedMessage20404 (message : OrderModifyCancelTrimmedMessage) -- 20404
  | orderConfirmationTrimmedMessage (message : OrderConfirmationTrimmedMessage) -- 20073
  | orderConfirmationTrimmedMessage20074 (message : OrderConfirmationTrimmedMessage) -- 20074
  | orderConfirmationTrimmedMessage20075 (message : OrderConfirmationTrimmedMessage) -- 20075
  | tradeConfirmationTrimmedMessage (message : TradeConfirmationTrimmedMessage) -- 20222
  | quickAcknowledgementMessage (message : QuickAcknowledgementMessage) -- 20401
  | quickAcknowledgementMessage20403 (message : QuickAcknowledgementMessage) -- 20403
  | quickAcknowledgementMessage20405 (message : QuickAcknowledgementMessage) -- 20405
  | quickAcknowledgementMessage20407 (message : QuickAcknowledgementMessage) -- 20407
  | quickAcknowledgementMessage20409 (message : QuickAcknowledgementMessage) -- 20409
  | quickAcknowledgementMessage20411 (message : QuickAcknowledgementMessage) -- 20411
  | quickAcknowledgementMessage20413 (message : QuickAcknowledgementMessage) -- 20413
  | quickAcknowledgementMessage20415 (message : QuickAcknowledgementMessage) -- 20415
  | quickAcknowledgementMessage20417 (message : QuickAcknowledgementMessage) -- 20417
  deriving DecidableEq, Repr

namespace MessagePayload

/-- The Transaction Code each message is sent under -/
def tag : MessagePayload → BitVec 16
  | .boardLotInTrimmedMessage _ => 20000
  | .boardLotInTrimmedMessage20400 _ => 20400
  | .orderModifyCancelTrimmedMessage _ => 20040
  | .orderModifyCancelTrimmedMessage20060 _ => 20060
  | .orderModifyCancelTrimmedMessage20070 _ => 20070
  | .orderModifyCancelTrimmedMessage20402 _ => 20402
  | .orderModifyCancelTrimmedMessage20404 _ => 20404
  | .orderConfirmationTrimmedMessage _ => 20073
  | .orderConfirmationTrimmedMessage20074 _ => 20074
  | .orderConfirmationTrimmedMessage20075 _ => 20075
  | .tradeConfirmationTrimmedMessage _ => 20222
  | .quickAcknowledgementMessage _ => 20401
  | .quickAcknowledgementMessage20403 _ => 20403
  | .quickAcknowledgementMessage20405 _ => 20405
  | .quickAcknowledgementMessage20407 _ => 20407
  | .quickAcknowledgementMessage20409 _ => 20409
  | .quickAcknowledgementMessage20411 _ => 20411
  | .quickAcknowledgementMessage20413 _ => 20413
  | .quickAcknowledgementMessage20415 _ => 20415
  | .quickAcknowledgementMessage20417 _ => 20417

def encode : MessagePayload → List UInt8
  | .boardLotInTrimmedMessage message => BoardLotInTrimmedMessage.encode message
  | .boardLotInTrimmedMessage20400 message => BoardLotInTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage message => OrderModifyCancelTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage20060 message => OrderModifyCancelTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage20070 message => OrderModifyCancelTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage20402 message => OrderModifyCancelTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage20404 message => OrderModifyCancelTrimmedMessage.encode message
  | .orderConfirmationTrimmedMessage message => OrderConfirmationTrimmedMessage.encode message
  | .orderConfirmationTrimmedMessage20074 message => OrderConfirmationTrimmedMessage.encode message
  | .orderConfirmationTrimmedMessage20075 message => OrderConfirmationTrimmedMessage.encode message
  | .tradeConfirmationTrimmedMessage message => TradeConfirmationTrimmedMessage.encode message
  | .quickAcknowledgementMessage message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20403 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20405 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20407 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20409 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20411 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20413 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20415 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20417 message => QuickAcknowledgementMessage.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessagePayload × List UInt8) :=
  if tag = 20000 then (BoardLotInTrimmedMessage.decode bytes).map fun (message, rest) => (.boardLotInTrimmedMessage message, rest)
  else if tag = 20400 then (BoardLotInTrimmedMessage.decode bytes).map fun (message, rest) => (.boardLotInTrimmedMessage20400 message, rest)
  else if tag = 20040 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage message, rest)
  else if tag = 20060 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage20060 message, rest)
  else if tag = 20070 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage20070 message, rest)
  else if tag = 20402 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage20402 message, rest)
  else if tag = 20404 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage20404 message, rest)
  else if tag = 20073 then (OrderConfirmationTrimmedMessage.decode bytes).map fun (message, rest) => (.orderConfirmationTrimmedMessage message, rest)
  else if tag = 20074 then (OrderConfirmationTrimmedMessage.decode bytes).map fun (message, rest) => (.orderConfirmationTrimmedMessage20074 message, rest)
  else if tag = 20075 then (OrderConfirmationTrimmedMessage.decode bytes).map fun (message, rest) => (.orderConfirmationTrimmedMessage20075 message, rest)
  else if tag = 20222 then (TradeConfirmationTrimmedMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationTrimmedMessage message, rest)
  else if tag = 20401 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage message, rest)
  else if tag = 20403 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20403 message, rest)
  else if tag = 20405 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20405 message, rest)
  else if tag = 20407 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20407 message, rest)
  else if tag = 20409 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20409 message, rest)
  else if tag = 20411 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20411 message, rest)
  else if tag = 20413 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20413 message, rest)
  else if tag = 20415 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20415 message, rest)
  else if tag = 20417 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20417 message, rest)
  else none

@[simp] theorem decode_encode (message : MessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessagePayload

/-- Message -/
structure Message where
  messagePayload : MessagePayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (MessagePayload.tag message.messagePayload)
    ++ (MessagePayload.encode message.messagePayload)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (messagePayload, bytes) ← MessagePayload.decode transactionCode bytes
  pure ({ messagePayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 240 := by
  unfold encode
  cases message.messagePayload with
  | boardLotInTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, BoardLotInTrimmedMessage.encode_length]
    omega
  | boardLotInTrimmedMessage20400 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, BoardLotInTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20060 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20070 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20402 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20404 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderConfirmationTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderConfirmationTrimmedMessage.encode_length]
    omega
  | orderConfirmationTrimmedMessage20074 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderConfirmationTrimmedMessage.encode_length]
    omega
  | orderConfirmationTrimmedMessage20075 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderConfirmationTrimmedMessage.encode_length]
    omega
  | tradeConfirmationTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, TradeConfirmationTrimmedMessage.encode_length]
    omega
  | quickAcknowledgementMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20403 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20405 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20407 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20409 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20411 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20413 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20415 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20417 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessagePayload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.NseNsefoOrderentryNnftrimmedV950
