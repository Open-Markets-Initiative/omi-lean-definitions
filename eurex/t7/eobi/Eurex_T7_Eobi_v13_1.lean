import Omi.Wire

/-!
# Eurex Exchange Enhanced Order Book Interface v13.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EobiFbeV131

/-- Eobi Header: 8 bytes -/
structure EobiHeader where
  bodyLen : BitVec 16
  templateId : BitVec 16
  msgSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EobiHeader

def encode (message : EobiHeader) : List UInt8 :=
  encodeUIntLE 2 message.bodyLen
    ++ encodeUIntLE 2 message.templateId
    ++ encodeUIntLE 4 message.msgSeqNum

def decode (bytes : List UInt8) : Option (EobiHeader × List UInt8) := do
  let (bodyLen, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ bodyLen, templateId, msgSeqNum }, bytes)

@[simp] theorem encode_length (message : EobiHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EobiHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EobiHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end EobiHeader

/-- Packet Header: 32 bytes -/
structure PacketHeader where
  eobiHeader : EobiHeader
  applSeqNum : BitVec 64
  marketSegmentId : BitVec 32
  partitionId : BitVec 8
  completionIndicator : BitVec 8
  applSeqResetIndicator : BitVec 8
  pad1 : Alpha 1
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace PacketHeader

def encode (message : PacketHeader) : List UInt8 :=
  EobiHeader.encode message.eobiHeader
    ++ encodeUIntLE 8 message.applSeqNum
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUInt 1 message.partitionId
    ++ encodeUInt 1 message.completionIndicator
    ++ encodeUInt 1 message.applSeqResetIndicator
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (PacketHeader × List UInt8) := do
  let (eobiHeader, bytes) ← EobiHeader.decode bytes
  let (applSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUInt 1 bytes
  let (completionIndicator, bytes) ← decodeUInt 1 bytes
  let (applSeqResetIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ eobiHeader, applSeqNum, marketSegmentId, partitionId, completionIndicator, applSeqResetIndicator, pad1, transactTime }, bytes)

@[simp] theorem encode_length (message : PacketHeader) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, EobiHeader.encode_length, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [EobiHeader.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end PacketHeader

/-- Instrmt Leg Grp Comp: 40 bytes -/
structure InstrmtLegGrpComp where
  legSymbol : BitVec 32
  pad4 : Alpha 4
  legSecurityId : BitVec 64
  legPrice : BitVec 64
  legRatioQty : BitVec 32
  legSecurityType : BitVec 8
  legSide : BitVec 8
  relatedPriceType : BitVec 8
  tradingStyle : BitVec 8
  relatedPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InstrmtLegGrpComp

def encode (message : InstrmtLegGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.legSymbol
    ++ Alpha.encode message.pad4
    ++ encodeUIntLE 8 message.legSecurityId
    ++ encodeUIntLE 8 message.legPrice
    ++ encodeUIntLE 4 message.legRatioQty
    ++ encodeUInt 1 message.legSecurityType
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.relatedPriceType
    ++ encodeUInt 1 message.tradingStyle
    ++ encodeUIntLE 8 message.relatedPrice

def decode (bytes : List UInt8) : Option (InstrmtLegGrpComp × List UInt8) := do
  let (legSymbol, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 4 bytes
  let (legSecurityType, bytes) ← decodeUInt 1 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (relatedPriceType, bytes) ← decodeUInt 1 bytes
  let (tradingStyle, bytes) ← decodeUInt 1 bytes
  let (relatedPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ legSymbol, pad4, legSecurityId, legPrice, legRatioQty, legSecurityType, legSide, relatedPriceType, tradingStyle, relatedPrice }, bytes)

@[simp] theorem encode_length (message : InstrmtLegGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : InstrmtLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmtLegGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end InstrmtLegGrpComp

/-- Add Complex Instrument -/
structure AddComplexInstrument where
  securityId : BitVec 64
  transactTime : BitVec 64
  securityDesc : Alpha 40
  securitySubType : BitVec 32
  productComplex : BitVec 8
  impliedMarketIndicator : BitVec 8
  quantityScalingFactor : BitVec 16
  legRatioMultiplier : BitVec 32
  pad2 : Alpha 2
  lastFragment : BitVec 8
  instrmtLegGrpComp : Bounded 1 InstrmtLegGrpComp
  deriving DecidableEq, Repr

namespace AddComplexInstrument

def encode (message : AddComplexInstrument) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.securityDesc
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.impliedMarketIndicator
    ++ encodeUIntLE 2 message.quantityScalingFactor
    ++ encodeUIntLE 4 message.legRatioMultiplier
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtLegGrpComp.val.length)
    ++ Alpha.encode message.pad2
    ++ encodeUInt 1 message.lastFragment
    ++ encodeMany InstrmtLegGrpComp.encode message.instrmtLegGrpComp.val

def decode (bytes : List UInt8) : Option (AddComplexInstrument × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityDesc, bytes) ← Alpha.decode 40 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (impliedMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (quantityScalingFactor, bytes) ← decodeUIntLE 2 bytes
  let (legRatioMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (instrmtLegGrpComp_, bytes) ← decodeMany InstrmtLegGrpComp.decode noLegs.toNat bytes
  if fits_instrmtLegGrpComp : instrmtLegGrpComp_.length < 256 ^ 1 then
    pure ({ securityId, transactTime, securityDesc, securitySubType, productComplex, impliedMarketIndicator, quantityScalingFactor, legRatioMultiplier, pad2, lastFragment, instrmtLegGrpComp := ⟨instrmtLegGrpComp_, fits_instrmtLegGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : AddComplexInstrument) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AddComplexInstrument) : (encode message).length ≤ 10272 := by
  have bound_instrmtLegGrpComp := message.instrmtLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const InstrmtLegGrpComp.encode 40 InstrmtLegGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : AddComplexInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 InstrmtLegGrpComp.encode InstrmtLegGrpComp.decode InstrmtLegGrpComp.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.instrmtLegGrpComp.length_lt, ↓reduceDIte]
  rfl

end AddComplexInstrument

/-- Add Flexible Instrument: 88 bytes -/
structure AddFlexibleInstrument where
  securityId : BitVec 64
  transactTime : BitVec 64
  securityDesc : Alpha 40
  securityType : BitVec 8
  putOrCall : BitVec 8
  exerciseStyle : BitVec 8
  settlMethod : BitVec 8
  maturityDate : BitVec 32
  strikePrice : BitVec 64
  optAttribute : BitVec 32
  contractDate : BitVec 32
  securityReferenceDataSupplement : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace AddFlexibleInstrument

def encode (message : AddFlexibleInstrument) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.securityDesc
    ++ encodeUInt 1 message.securityType
    ++ encodeUInt 1 message.putOrCall
    ++ encodeUInt 1 message.exerciseStyle
    ++ encodeUInt 1 message.settlMethod
    ++ encodeUIntLE 4 message.maturityDate
    ++ encodeUIntLE 8 message.strikePrice
    ++ encodeUIntLE 4 message.optAttribute
    ++ encodeUIntLE 4 message.contractDate
    ++ encodeUIntLE 4 message.securityReferenceDataSupplement
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (AddFlexibleInstrument × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityDesc, bytes) ← Alpha.decode 40 bytes
  let (securityType, bytes) ← decodeUInt 1 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (settlMethod, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (optAttribute, bytes) ← decodeUIntLE 4 bytes
  let (contractDate, bytes) ← decodeUIntLE 4 bytes
  let (securityReferenceDataSupplement, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ securityId, transactTime, securityDesc, securityType, putOrCall, exerciseStyle, settlMethod, maturityDate, strikePrice, optAttribute, contractDate, securityReferenceDataSupplement, pad4 }, bytes)

@[simp] theorem encode_length (message : AddFlexibleInstrument) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AddFlexibleInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddFlexibleInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AddFlexibleInstrument

/-- Related Instrument Grp Comp: 8 bytes -/
structure RelatedInstrumentGrpComp where
  relatedSecurityId : BitVec 64
  deriving DecidableEq, Repr

namespace RelatedInstrumentGrpComp

def encode (message : RelatedInstrumentGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.relatedSecurityId

def decode (bytes : List UInt8) : Option (RelatedInstrumentGrpComp × List UInt8) := do
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  pure ({ relatedSecurityId }, bytes)

@[simp] theorem encode_length (message : RelatedInstrumentGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RelatedInstrumentGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RelatedInstrumentGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RelatedInstrumentGrpComp

/-- Add Scaled Simple Instrument: 72 bytes -/
structure AddScaledSimpleInstrument where
  securityId : BitVec 64
  transactTime : BitVec 64
  securityDesc : Alpha 40
  securityType : BitVec 8
  pad1 : Alpha 1
  quantityScalingFactor : BitVec 16
  pad4 : Alpha 4
  relatedInstrumentGrpComp : RelatedInstrumentGrpComp
  deriving DecidableEq, Repr

namespace AddScaledSimpleInstrument

def encode (message : AddScaledSimpleInstrument) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.securityDesc
    ++ encodeUInt 1 message.securityType
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 2 message.quantityScalingFactor
    ++ Alpha.encode message.pad4
    ++ RelatedInstrumentGrpComp.encode message.relatedInstrumentGrpComp

def decode (bytes : List UInt8) : Option (AddScaledSimpleInstrument × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityDesc, bytes) ← Alpha.decode 40 bytes
  let (securityType, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (quantityScalingFactor, bytes) ← decodeUIntLE 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (relatedInstrumentGrpComp, bytes) ← RelatedInstrumentGrpComp.decode bytes
  pure ({ securityId, transactTime, securityDesc, securityType, pad1, quantityScalingFactor, pad4, relatedInstrumentGrpComp }, bytes)

@[simp] theorem encode_length (message : AddScaledSimpleInstrument) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, RelatedInstrumentGrpComp.encode_length]

theorem encode_length_pos (message : AddScaledSimpleInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddScaledSimpleInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RelatedInstrumentGrpComp.decode_encode, Option.bind_some]
  rfl

end AddScaledSimpleInstrument

/-- Auction Bbo: 52 bytes -/
structure AuctionBbo where
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  bidSize : BitVec 64
  offerSize : BitVec 64
  potentialSecurityTradingEvent : BitVec 8
  bidOrdType : BitVec 8
  offerOrdType : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace AuctionBbo

def encode (message : AuctionBbo) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.bidSize
    ++ encodeUIntLE 8 message.offerSize
    ++ encodeUInt 1 message.potentialSecurityTradingEvent
    ++ encodeUInt 1 message.bidOrdType
    ++ encodeUInt 1 message.offerOrdType
    ++ Alpha.encode message.pad1

def decode (bytes : List UInt8) : Option (AuctionBbo × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (potentialSecurityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (bidOrdType, bytes) ← decodeUInt 1 bytes
  let (offerOrdType, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ transactTime, securityId, bidPx, offerPx, bidSize, offerSize, potentialSecurityTradingEvent, bidOrdType, offerOrdType, pad1 }, bytes)

@[simp] theorem encode_length (message : AuctionBbo) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AuctionBbo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionBbo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AuctionBbo

/-- Auction Clearing Price: 48 bytes -/
structure AuctionClearingPrice where
  transactTime : BitVec 64
  securityId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  imbalanceQty : BitVec 64
  securityTradingStatus : BitVec 8
  potentialSecurityTradingEvent : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace AuctionClearingPrice

def encode (message : AuctionClearingPrice) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.imbalanceQty
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.potentialSecurityTradingEvent
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (AuctionClearingPrice × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQty, bytes) ← decodeUIntLE 8 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (potentialSecurityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ transactTime, securityId, lastPx, lastQty, imbalanceQty, securityTradingStatus, potentialSecurityTradingEvent, pad6 }, bytes)

@[simp] theorem encode_length (message : AuctionClearingPrice) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AuctionClearingPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionClearingPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AuctionClearingPrice

/-- Cross Request: 36 bytes -/
structure CrossRequest where
  securityId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  side : BitVec 8
  crossRequestType : BitVec 8
  inputSource : BitVec 8
  pad1 : Alpha 1
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace CrossRequest

def encode (message : CrossRequest) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.crossRequestType
    ++ encodeUInt 1 message.inputSource
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (CrossRequest × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (crossRequestType, bytes) ← decodeUInt 1 bytes
  let (inputSource, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, lastPx, lastQty, side, crossRequestType, inputSource, pad1, transactTime }, bytes)

@[simp] theorem encode_length (message : CrossRequest) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CrossRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end CrossRequest

/-- Remaining Order Details Comp: 24 bytes -/
structure RemainingOrderDetailsComp where
  trdRegTsPrevTimePriority : BitVec 64
  displayQty : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace RemainingOrderDetailsComp

def encode (message : RemainingOrderDetailsComp) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsPrevTimePriority
    ++ encodeUIntLE 8 message.displayQty
    ++ encodeUIntLE 8 message.price

def decode (bytes : List UInt8) : Option (RemainingOrderDetailsComp × List UInt8) := do
  let (trdRegTsPrevTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ trdRegTsPrevTimePriority, displayQty, price }, bytes)

@[simp] theorem encode_length (message : RemainingOrderDetailsComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RemainingOrderDetailsComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RemainingOrderDetailsComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RemainingOrderDetailsComp

/-- Execution Summary: 96 bytes -/
structure ExecutionSummary where
  securityId : BitVec 64
  requestTime : BitVec 64
  execId : BitVec 64
  lastQty : BitVec 64
  aggressorSide : BitVec 8
  pad1 : Alpha 1
  tradeCondition : BitVec 16
  tradingHhiIndicator : BitVec 8
  pad3 : Alpha 3
  lastPx : BitVec 64
  remainingOrderDetailsComp : RemainingOrderDetailsComp
  restingHiddenQty : BitVec 64
  restingCxlQty : BitVec 64
  aggressorTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionSummary

def encode (message : ExecutionSummary) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUInt 1 message.aggressorSide
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 2 message.tradeCondition
    ++ encodeUInt 1 message.tradingHhiIndicator
    ++ Alpha.encode message.pad3
    ++ encodeUIntLE 8 message.lastPx
    ++ RemainingOrderDetailsComp.encode message.remainingOrderDetailsComp
    ++ encodeUIntLE 8 message.restingHiddenQty
    ++ encodeUIntLE 8 message.restingCxlQty
    ++ encodeUIntLE 8 message.aggressorTime

def decode (bytes : List UInt8) : Option (ExecutionSummary × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (tradingHhiIndicator, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (remainingOrderDetailsComp, bytes) ← RemainingOrderDetailsComp.decode bytes
  let (restingHiddenQty, bytes) ← decodeUIntLE 8 bytes
  let (restingCxlQty, bytes) ← decodeUIntLE 8 bytes
  let (aggressorTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, requestTime, execId, lastQty, aggressorSide, pad1, tradeCondition, tradingHhiIndicator, pad3, lastPx, remainingOrderDetailsComp, restingHiddenQty, restingCxlQty, aggressorTime }, bytes)

@[simp] theorem encode_length (message : ExecutionSummary) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, RemainingOrderDetailsComp.encode_length]

theorem encode_length_pos (message : ExecutionSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [RemainingOrderDetailsComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ExecutionSummary

/-- Full Order Execution: 48 bytes -/
structure FullOrderExecution where
  side : BitVec 8
  ordType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  hhiIndicator : BitVec 8
  trdMatchId : BitVec 32
  price : BitVec 64
  trdRegTsTimePriority : BitVec 64
  securityId : BitVec 64
  lastQty : BitVec 64
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace FullOrderExecution

def encode (message : FullOrderExecution) : List UInt8 :=
  encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.algorithmicTradeIndicator
    ++ encodeUInt 1 message.hhiIndicator
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.lastPx

def decode (bytes : List UInt8) : Option (FullOrderExecution × List UInt8) := do
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUInt 1 bytes
  let (hhiIndicator, bytes) ← decodeUInt 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, ordType, algorithmicTradeIndicator, hhiIndicator, trdMatchId, price, trdRegTsTimePriority, securityId, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : FullOrderExecution) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : FullOrderExecution) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FullOrderExecution) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end FullOrderExecution

/-- Heartbeat: 8 bytes -/
structure Heartbeat where
  lastMsgSeqNumProcessed : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (message : Heartbeat) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ lastMsgSeqNumProcessed, pad4 }, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : Heartbeat) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end Heartbeat

/-- Instrument State Change: 48 bytes -/
structure InstrumentStateChange where
  securityId : BitVec 64
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  securityTradingEvent : BitVec 8
  soldOutIndicator : BitVec 8
  pad2 : Alpha 2
  highPx : BitVec 64
  lowPx : BitVec 64
  transactTime : BitVec 64
  tesSecurityStatus : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace InstrumentStateChange

def encode (message : InstrumentStateChange) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUInt 1 message.securityStatus
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.securityTradingEvent
    ++ encodeUInt 1 message.soldOutIndicator
    ++ Alpha.encode message.pad2
    ++ encodeUIntLE 8 message.highPx
    ++ encodeUIntLE 8 message.lowPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUInt 1 message.tesSecurityStatus
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (InstrumentStateChange × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (securityStatus, bytes) ← decodeUInt 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (soldOutIndicator, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (highPx, bytes) ← decodeUIntLE 8 bytes
  let (lowPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tesSecurityStatus, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ securityId, securityStatus, securityTradingStatus, marketCondition, fastMarketIndicator, securityTradingEvent, soldOutIndicator, pad2, highPx, lowPx, transactTime, tesSecurityStatus, pad7 }, bytes)

@[simp] theorem encode_length (message : InstrumentStateChange) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InstrumentStateChange

/-- Md Instrument Entry Grp Comp: 32 bytes -/
structure MdInstrumentEntryGrpComp where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdOriginType : BitVec 8
  mdEntryType : BitVec 8
  tradeCondition : BitVec 16
  trdType : BitVec 16
  multiLegReportingType : BitVec 8
  multiLegPriceModel : BitVec 8
  nonDisclosedTradeVolume : BitVec 64
  deriving DecidableEq, Repr

namespace MdInstrumentEntryGrpComp

def encode (message : MdInstrumentEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUInt 1 message.mdOriginType
    ++ encodeUInt 1 message.mdEntryType
    ++ encodeUIntLE 2 message.tradeCondition
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.multiLegReportingType
    ++ encodeUInt 1 message.multiLegPriceModel
    ++ encodeUIntLE 8 message.nonDisclosedTradeVolume

def decode (bytes : List UInt8) : Option (MdInstrumentEntryGrpComp × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdOriginType, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (multiLegReportingType, bytes) ← decodeUInt 1 bytes
  let (multiLegPriceModel, bytes) ← decodeUInt 1 bytes
  let (nonDisclosedTradeVolume, bytes) ← decodeUIntLE 8 bytes
  pure ({ mdEntryPx, mdEntrySize, mdOriginType, mdEntryType, tradeCondition, trdType, multiLegReportingType, multiLegPriceModel, nonDisclosedTradeVolume }, bytes)

@[simp] theorem encode_length (message : MdInstrumentEntryGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MdInstrumentEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdInstrumentEntryGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end MdInstrumentEntryGrpComp

/-- Instrument Summary -/
structure InstrumentSummary where
  securityId : BitVec 64
  lastUpdateTime : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  totNoOrders : BitVec 16
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  securityTradingEvent : BitVec 8
  soldOutIndicator : BitVec 8
  highPx : BitVec 64
  lowPx : BitVec 64
  productComplex : BitVec 8
  tesSecurityStatus : BitVec 8
  pad1 : Alpha 1
  mdInstrumentEntryGrpComp : Bounded 1 MdInstrumentEntryGrpComp
  deriving DecidableEq, Repr

namespace InstrumentSummary

def encode (message : InstrumentSummary) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ encodeUIntLE 2 message.totNoOrders
    ++ encodeUInt 1 message.securityStatus
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.securityTradingEvent
    ++ encodeUInt 1 message.soldOutIndicator
    ++ encodeUIntLE 8 message.highPx
    ++ encodeUIntLE 8 message.lowPx
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.mdInstrumentEntryGrpComp.val.length)
    ++ encodeUInt 1 message.tesSecurityStatus
    ++ Alpha.encode message.pad1
    ++ encodeMany MdInstrumentEntryGrpComp.encode message.mdInstrumentEntryGrpComp.val

def decode (bytes : List UInt8) : Option (InstrumentSummary × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (totNoOrders, bytes) ← decodeUIntLE 2 bytes
  let (securityStatus, bytes) ← decodeUInt 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (soldOutIndicator, bytes) ← decodeUInt 1 bytes
  let (highPx, bytes) ← decodeUIntLE 8 bytes
  let (lowPx, bytes) ← decodeUIntLE 8 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (noMdEntries, bytes) ← decodeUInt 1 bytes
  let (tesSecurityStatus, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (mdInstrumentEntryGrpComp_, bytes) ← decodeMany MdInstrumentEntryGrpComp.decode noMdEntries.toNat bytes
  if fits_mdInstrumentEntryGrpComp : mdInstrumentEntryGrpComp_.length < 256 ^ 1 then
    pure ({ securityId, lastUpdateTime, trdRegTsExecutionTime, totNoOrders, securityStatus, securityTradingStatus, marketCondition, fastMarketIndicator, securityTradingEvent, soldOutIndicator, highPx, lowPx, productComplex, tesSecurityStatus, pad1, mdInstrumentEntryGrpComp := ⟨mdInstrumentEntryGrpComp_, fits_mdInstrumentEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstrumentSummary) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentSummary) : (encode message).length ≤ 8212 := by
  have bound_mdInstrumentEntryGrpComp := message.mdInstrumentEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, encodeMany_length_const MdInstrumentEntryGrpComp.encode 32 MdInstrumentEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InstrumentSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 MdInstrumentEntryGrpComp.encode MdInstrumentEntryGrpComp.decode MdInstrumentEntryGrpComp.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.mdInstrumentEntryGrpComp.length_lt, ↓reduceDIte]
  rfl

end InstrumentSummary

/-- Sec Mass Stat Grp Comp: 32 bytes -/
structure SecMassStatGrpComp where
  securityId : BitVec 64
  highPx : BitVec 64
  lowPx : BitVec 64
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  marketCondition : BitVec 8
  securityTradingEvent : BitVec 8
  soldOutIndicator : BitVec 8
  tesSecurityStatus : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace SecMassStatGrpComp

def encode (message : SecMassStatGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.highPx
    ++ encodeUIntLE 8 message.lowPx
    ++ encodeUInt 1 message.securityStatus
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.securityTradingEvent
    ++ encodeUInt 1 message.soldOutIndicator
    ++ encodeUInt 1 message.tesSecurityStatus
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (SecMassStatGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (highPx, bytes) ← decodeUIntLE 8 bytes
  let (lowPx, bytes) ← decodeUIntLE 8 bytes
  let (securityStatus, bytes) ← decodeUInt 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (soldOutIndicator, bytes) ← decodeUInt 1 bytes
  let (tesSecurityStatus, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityId, highPx, lowPx, securityStatus, securityTradingStatus, marketCondition, securityTradingEvent, soldOutIndicator, tesSecurityStatus, pad2 }, bytes)

@[simp] theorem encode_length (message : SecMassStatGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecMassStatGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecMassStatGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SecMassStatGrpComp

/-- Mass Instrument State Change -/
structure MassInstrumentStateChange where
  instrumentScopeProductComplex : BitVec 8
  securityMassStatus : BitVec 8
  securityMassTradingStatus : BitVec 8
  massMarketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  securityMassTradingEvent : BitVec 8
  massSoldOutIndicator : BitVec 8
  tesSecurityMassStatus : BitVec 8
  transactTime : BitVec 64
  lastFragment : BitVec 8
  pad6 : Alpha 6
  secMassStatGrpComp : Bounded 1 SecMassStatGrpComp
  deriving DecidableEq, Repr

namespace MassInstrumentStateChange

def encode (message : MassInstrumentStateChange) : List UInt8 :=
  encodeUInt 1 message.instrumentScopeProductComplex
    ++ encodeUInt 1 message.securityMassStatus
    ++ encodeUInt 1 message.securityMassTradingStatus
    ++ encodeUInt 1 message.massMarketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.securityMassTradingEvent
    ++ encodeUInt 1 message.massSoldOutIndicator
    ++ encodeUInt 1 message.tesSecurityMassStatus
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUInt 1 message.lastFragment
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.secMassStatGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany SecMassStatGrpComp.encode message.secMassStatGrpComp.val

def decode (bytes : List UInt8) : Option (MassInstrumentStateChange × List UInt8) := do
  let (instrumentScopeProductComplex, bytes) ← decodeUInt 1 bytes
  let (securityMassStatus, bytes) ← decodeUInt 1 bytes
  let (securityMassTradingStatus, bytes) ← decodeUInt 1 bytes
  let (massMarketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (securityMassTradingEvent, bytes) ← decodeUInt 1 bytes
  let (massSoldOutIndicator, bytes) ← decodeUInt 1 bytes
  let (tesSecurityMassStatus, bytes) ← decodeUInt 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (noRelatedSym, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (secMassStatGrpComp_, bytes) ← decodeMany SecMassStatGrpComp.decode noRelatedSym.toNat bytes
  if fits_secMassStatGrpComp : secMassStatGrpComp_.length < 256 ^ 1 then
    pure ({ instrumentScopeProductComplex, securityMassStatus, securityMassTradingStatus, massMarketCondition, fastMarketIndicator, securityMassTradingEvent, massSoldOutIndicator, tesSecurityMassStatus, transactTime, lastFragment, pad6, secMassStatGrpComp := ⟨secMassStatGrpComp_, fits_secMassStatGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassInstrumentStateChange) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassInstrumentStateChange) : (encode message).length ≤ 8184 := by
  have bound_secMassStatGrpComp := message.secMassStatGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const SecMassStatGrpComp.encode 32 SecMassStatGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MassInstrumentStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 SecMassStatGrpComp.encode SecMassStatGrpComp.decode SecMassStatGrpComp.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.secMassStatGrpComp.length_lt, ↓reduceDIte]
  rfl

end MassInstrumentStateChange

/-- Order Details Comp: 28 bytes -/
structure OrderDetailsComp where
  trdRegTsTimePriority : BitVec 64
  displayQty : BitVec 64
  side : BitVec 8
  ordType : BitVec 8
  hhiIndicator : BitVec 8
  pad1 : Alpha 1
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDetailsComp

def encode (message : OrderDetailsComp) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.displayQty
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.hhiIndicator
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 8 message.price

def decode (bytes : List UInt8) : Option (OrderDetailsComp × List UInt8) := do
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (hhiIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ trdRegTsTimePriority, displayQty, side, ordType, hhiIndicator, pad1, price }, bytes)

@[simp] theorem encode_length (message : OrderDetailsComp) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderDetailsComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDetailsComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OrderDetailsComp

/-- Order Add: 44 bytes -/
structure OrderAdd where
  requestTime : BitVec 64
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderAdd

def encode (message : OrderAdd) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderAdd × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ requestTime, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderAdd) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderAdd) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAdd) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderAdd

/-- Order Delete: 52 bytes -/
structure OrderDelete where
  requestTime : BitVec 64
  transactTime : BitVec 64
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderDelete

def encode (message : OrderDelete) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderDelete × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ requestTime, transactTime, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderDelete) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderDelete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDelete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderDelete

/-- Order Mass Delete: 16 bytes -/
structure OrderMassDelete where
  securityId : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderMassDelete

def encode (message : OrderMassDelete) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (OrderMassDelete × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, transactTime }, bytes)

@[simp] theorem encode_length (message : OrderMassDelete) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderMassDelete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassDelete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OrderMassDelete

/-- Order Modify: 76 bytes -/
structure OrderModify where
  requestTime : BitVec 64
  trdRegTsPrevTimePriority : BitVec 64
  prevPrice : BitVec 64
  prevDisplayQty : BitVec 64
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  prevPriceHhiIndicator : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace OrderModify

def encode (message : OrderModify) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.trdRegTsPrevTimePriority
    ++ encodeUIntLE 8 message.prevPrice
    ++ encodeUIntLE 8 message.prevDisplayQty
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp
    ++ encodeUInt 1 message.prevPriceHhiIndicator
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (OrderModify × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsPrevTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (prevPrice, bytes) ← decodeUIntLE 8 bytes
  let (prevDisplayQty, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  let (prevPriceHhiIndicator, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ requestTime, trdRegTsPrevTimePriority, prevPrice, prevDisplayQty, securityId, orderDetailsComp, prevPriceHhiIndicator, pad7 }, bytes)

@[simp] theorem encode_length (message : OrderModify) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetailsComp.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModify) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModify) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderModify

/-- Order Modify Same Prio: 60 bytes -/
structure OrderModifySamePrio where
  requestTime : BitVec 64
  transactTime : BitVec 64
  prevDisplayQty : BitVec 64
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderModifySamePrio

def encode (message : OrderModifySamePrio) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.prevDisplayQty
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderModifySamePrio × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (prevDisplayQty, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ requestTime, transactTime, prevDisplayQty, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderModifySamePrio) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderModifySamePrio) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifySamePrio) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderModifySamePrio

/-- Partial Order Execution: 48 bytes -/
structure PartialOrderExecution where
  side : BitVec 8
  ordType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  hhiIndicator : BitVec 8
  trdMatchId : BitVec 32
  price : BitVec 64
  trdRegTsTimePriority : BitVec 64
  securityId : BitVec 64
  lastQty : BitVec 64
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace PartialOrderExecution

def encode (message : PartialOrderExecution) : List UInt8 :=
  encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.algorithmicTradeIndicator
    ++ encodeUInt 1 message.hhiIndicator
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.lastPx

def decode (bytes : List UInt8) : Option (PartialOrderExecution × List UInt8) := do
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUInt 1 bytes
  let (hhiIndicator, bytes) ← decodeUInt 1 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, ordType, algorithmicTradeIndicator, hhiIndicator, trdMatchId, price, trdRegTsTimePriority, securityId, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : PartialOrderExecution) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : PartialOrderExecution) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialOrderExecution) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end PartialOrderExecution

/-- Product State Change: 16 bytes -/
structure ProductStateChange where
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  tesTradSesStatus : BitVec 8
  pad2 : Alpha 2
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ProductStateChange

def encode (message : ProductStateChange) : List UInt8 :=
  encodeUInt 1 message.tradingSessionId
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.tradSesStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.tesTradSesStatus
    ++ Alpha.encode message.pad2
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (ProductStateChange × List UInt8) := do
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (tesTradSesStatus, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradingSessionId, tradingSessionSubId, tradSesStatus, marketCondition, fastMarketIndicator, tesTradSesStatus, pad2, transactTime }, bytes)

@[simp] theorem encode_length (message : ProductStateChange) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ProductStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ProductStateChange

/-- Product Summary: 16 bytes -/
structure ProductSummary where
  lastMsgSeqNumProcessed : BitVec 32
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  tesTradSesStatus : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ProductSummary

def encode (message : ProductSummary) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ encodeUInt 1 message.tradingSessionId
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.tradSesStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.tesTradSesStatus
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (ProductSummary × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (tesTradSesStatus, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ lastMsgSeqNumProcessed, tradingSessionId, tradingSessionSubId, tradSesStatus, marketCondition, fastMarketIndicator, tesTradSesStatus, pad6 }, bytes)

@[simp] theorem encode_length (message : ProductSummary) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ProductSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ProductSummary

/-- Quote Request: 32 bytes -/
structure QuoteRequest where
  securityId : BitVec 64
  lastQty : BitVec 64
  side : BitVec 8
  pad7 : Alpha 7
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.pad7
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, lastQty, side, pad7, transactTime }, bytes)

@[simp] theorem encode_length (message : QuoteRequest) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteRequest

/-- Snapshot Order: 28 bytes -/
structure SnapshotOrder where
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace SnapshotOrder

def encode (message : SnapshotOrder) : List UInt8 :=
  OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (SnapshotOrder × List UInt8) := do
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : SnapshotOrder) : (encode message).length = 28 := by
  unfold encode
  simp only [OrderDetailsComp.encode_length]

theorem encode_length_pos (message : SnapshotOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end SnapshotOrder

/-- Tes Trade Report: 72 bytes -/
structure TesTradeReport where
  securityId : BitVec 64
  transactTime : BitVec 64
  lastQty : BitVec 64
  lastPx : BitVec 64
  trdMatchId : BitVec 32
  trdType : BitVec 16
  tradeCondition : BitVec 16
  multiLegReportingType : BitVec 8
  multiLegPriceModel : BitVec 8
  pad6 : Alpha 6
  nonDisclosedTradeVolume : BitVec 64
  transBkdTime : BitVec 64
  numberOfBuySides : BitVec 16
  numberOfSellSides : BitVec 16
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace TesTradeReport

def encode (message : TesTradeReport) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUIntLE 2 message.tradeCondition
    ++ encodeUInt 1 message.multiLegReportingType
    ++ encodeUInt 1 message.multiLegPriceModel
    ++ Alpha.encode message.pad6
    ++ encodeUIntLE 8 message.nonDisclosedTradeVolume
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 2 message.numberOfBuySides
    ++ encodeUIntLE 2 message.numberOfSellSides
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (TesTradeReport × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (multiLegReportingType, bytes) ← decodeUInt 1 bytes
  let (multiLegPriceModel, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (nonDisclosedTradeVolume, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (numberOfBuySides, bytes) ← decodeUIntLE 2 bytes
  let (numberOfSellSides, bytes) ← decodeUIntLE 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ securityId, transactTime, lastQty, lastPx, trdMatchId, trdType, tradeCondition, multiLegReportingType, multiLegPriceModel, pad6, nonDisclosedTradeVolume, transBkdTime, numberOfBuySides, numberOfSellSides, pad4 }, bytes)

@[simp] theorem encode_length (message : TesTradeReport) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TesTradeReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesTradeReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TesTradeReport

/-- Top Of Book: 56 bytes -/
structure TopOfBook where
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  bidSize : BitVec 64
  offerSize : BitVec 64
  numberOfBuyOrders : BitVec 16
  numberOfSellOrders : BitVec 16
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace TopOfBook

def encode (message : TopOfBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.bidSize
    ++ encodeUIntLE 8 message.offerSize
    ++ encodeUIntLE 2 message.numberOfBuyOrders
    ++ encodeUIntLE 2 message.numberOfSellOrders
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (TopOfBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (numberOfBuyOrders, bytes) ← decodeUIntLE 2 bytes
  let (numberOfSellOrders, bytes) ← decodeUIntLE 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ transactTime, securityId, bidPx, offerPx, bidSize, offerSize, numberOfBuyOrders, numberOfSellOrders, pad4 }, bytes)

@[simp] theorem encode_length (message : TopOfBook) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TopOfBook) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TopOfBook

/-- Trade Report: 48 bytes -/
structure TradeReport where
  securityId : BitVec 64
  transactTime : BitVec 64
  lastQty : BitVec 64
  lastPx : BitVec 64
  trdMatchId : BitVec 32
  matchType : BitVec 8
  matchSubType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  pad1 : Alpha 1
  tradeCondition : BitVec 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace TradeReport

def encode (message : TradeReport) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUInt 1 message.matchType
    ++ encodeUInt 1 message.matchSubType
    ++ encodeUInt 1 message.algorithmicTradeIndicator
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 2 message.tradeCondition
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (TradeReport × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (matchSubType, bytes) ← decodeUInt 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ securityId, transactTime, lastQty, lastPx, trdMatchId, matchType, matchSubType, algorithmicTradeIndicator, pad1, tradeCondition, pad6 }, bytes)

@[simp] theorem encode_length (message : TradeReport) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradeReport

/-- Md Trade Entry Grp Comp: 24 bytes -/
structure MdTradeEntryGrpComp where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryType : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace MdTradeEntryGrpComp

def encode (message : MdTradeEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUInt 1 message.mdEntryType
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (MdTradeEntryGrpComp × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryType, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ mdEntryPx, mdEntrySize, mdEntryType, pad7 }, bytes)

@[simp] theorem encode_length (message : MdTradeEntryGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MdTradeEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdTradeEntryGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end MdTradeEntryGrpComp

/-- Trade Reversal -/
structure TradeReversal where
  securityId : BitVec 64
  transactTime : BitVec 64
  lastQty : BitVec 64
  lastPx : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  trdMatchId : BitVec 32
  tradeCondition : BitVec 16
  mdOriginType : BitVec 8
  mdTradeEntryGrpComp : Bounded 1 MdTradeEntryGrpComp
  deriving DecidableEq, Repr

namespace TradeReversal

def encode (message : TradeReversal) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 2 message.tradeCondition
    ++ encodeUInt 1 message.mdOriginType
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.mdTradeEntryGrpComp.val.length)
    ++ encodeMany MdTradeEntryGrpComp.encode message.mdTradeEntryGrpComp.val

def decode (bytes : List UInt8) : Option (TradeReversal × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition, bytes) ← decodeUIntLE 2 bytes
  let (mdOriginType, bytes) ← decodeUInt 1 bytes
  let (noMdEntries, bytes) ← decodeUInt 1 bytes
  let (mdTradeEntryGrpComp_, bytes) ← decodeMany MdTradeEntryGrpComp.decode noMdEntries.toNat bytes
  if fits_mdTradeEntryGrpComp : mdTradeEntryGrpComp_.length < 256 ^ 1 then
    pure ({ securityId, transactTime, lastQty, lastPx, trdRegTsExecutionTime, trdMatchId, tradeCondition, mdOriginType, mdTradeEntryGrpComp := ⟨mdTradeEntryGrpComp_, fits_mdTradeEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeReversal) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeReversal) : (encode message).length ≤ 6168 := by
  have bound_mdTradeEntryGrpComp := message.mdTradeEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MdTradeEntryGrpComp.encode 24 MdTradeEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeReversal) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 MdTradeEntryGrpComp.encode MdTradeEntryGrpComp.decode MdTradeEntryGrpComp.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.mdTradeEntryGrpComp.length_lt, ↓reduceDIte]
  rfl

end TradeReversal

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | addComplexInstrument (message : AddComplexInstrument) -- 13400
  | addFlexibleInstrument (message : AddFlexibleInstrument) -- 13401
  | addScaledSimpleInstrument (message : AddScaledSimpleInstrument) -- 13402
  | auctionBbo (message : AuctionBbo) -- 13500
  | auctionClearingPrice (message : AuctionClearingPrice) -- 13501
  | crossRequest (message : CrossRequest) -- 13502
  | executionSummary (message : ExecutionSummary) -- 13202
  | fullOrderExecution (message : FullOrderExecution) -- 13104
  | heartbeat (message : Heartbeat) -- 13001
  | instrumentStateChange (message : InstrumentStateChange) -- 13301
  | instrumentSummary (message : InstrumentSummary) -- 13601
  | massInstrumentStateChange (message : MassInstrumentStateChange) -- 13302
  | orderAdd (message : OrderAdd) -- 13100
  | orderDelete (message : OrderDelete) -- 13102
  | orderMassDelete (message : OrderMassDelete) -- 13103
  | orderModify (message : OrderModify) -- 13101
  | orderModifySamePrio (message : OrderModifySamePrio) -- 13106
  | partialOrderExecution (message : PartialOrderExecution) -- 13105
  | productStateChange (message : ProductStateChange) -- 13300
  | productSummary (message : ProductSummary) -- 13600
  | quoteRequest (message : QuoteRequest) -- 13503
  | snapshotOrder (message : SnapshotOrder) -- 13602
  | tesTradeReport (message : TesTradeReport) -- 13203
  | topOfBook (message : TopOfBook) -- 13504
  | tradeReport (message : TradeReport) -- 13201
  | tradeReversal (message : TradeReversal) -- 13200
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .addComplexInstrument _ => 13400
  | .addFlexibleInstrument _ => 13401
  | .addScaledSimpleInstrument _ => 13402
  | .auctionBbo _ => 13500
  | .auctionClearingPrice _ => 13501
  | .crossRequest _ => 13502
  | .executionSummary _ => 13202
  | .fullOrderExecution _ => 13104
  | .heartbeat _ => 13001
  | .instrumentStateChange _ => 13301
  | .instrumentSummary _ => 13601
  | .massInstrumentStateChange _ => 13302
  | .orderAdd _ => 13100
  | .orderDelete _ => 13102
  | .orderMassDelete _ => 13103
  | .orderModify _ => 13101
  | .orderModifySamePrio _ => 13106
  | .partialOrderExecution _ => 13105
  | .productStateChange _ => 13300
  | .productSummary _ => 13600
  | .quoteRequest _ => 13503
  | .snapshotOrder _ => 13602
  | .tesTradeReport _ => 13203
  | .topOfBook _ => 13504
  | .tradeReport _ => 13201
  | .tradeReversal _ => 13200

def encode : Payload → List UInt8
  | .addComplexInstrument message => AddComplexInstrument.encode message
  | .addFlexibleInstrument message => AddFlexibleInstrument.encode message
  | .addScaledSimpleInstrument message => AddScaledSimpleInstrument.encode message
  | .auctionBbo message => AuctionBbo.encode message
  | .auctionClearingPrice message => AuctionClearingPrice.encode message
  | .crossRequest message => CrossRequest.encode message
  | .executionSummary message => ExecutionSummary.encode message
  | .fullOrderExecution message => FullOrderExecution.encode message
  | .heartbeat message => Heartbeat.encode message
  | .instrumentStateChange message => InstrumentStateChange.encode message
  | .instrumentSummary message => InstrumentSummary.encode message
  | .massInstrumentStateChange message => MassInstrumentStateChange.encode message
  | .orderAdd message => OrderAdd.encode message
  | .orderDelete message => OrderDelete.encode message
  | .orderMassDelete message => OrderMassDelete.encode message
  | .orderModify message => OrderModify.encode message
  | .orderModifySamePrio message => OrderModifySamePrio.encode message
  | .partialOrderExecution message => PartialOrderExecution.encode message
  | .productStateChange message => ProductStateChange.encode message
  | .productSummary message => ProductSummary.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .snapshotOrder message => SnapshotOrder.encode message
  | .tesTradeReport message => TesTradeReport.encode message
  | .topOfBook message => TopOfBook.encode message
  | .tradeReport message => TradeReport.encode message
  | .tradeReversal message => TradeReversal.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 13400 then (AddComplexInstrument.decode bytes).map fun (message, rest) => (.addComplexInstrument message, rest)
  else if tag = 13401 then (AddFlexibleInstrument.decode bytes).map fun (message, rest) => (.addFlexibleInstrument message, rest)
  else if tag = 13402 then (AddScaledSimpleInstrument.decode bytes).map fun (message, rest) => (.addScaledSimpleInstrument message, rest)
  else if tag = 13500 then (AuctionBbo.decode bytes).map fun (message, rest) => (.auctionBbo message, rest)
  else if tag = 13501 then (AuctionClearingPrice.decode bytes).map fun (message, rest) => (.auctionClearingPrice message, rest)
  else if tag = 13502 then (CrossRequest.decode bytes).map fun (message, rest) => (.crossRequest message, rest)
  else if tag = 13202 then (ExecutionSummary.decode bytes).map fun (message, rest) => (.executionSummary message, rest)
  else if tag = 13104 then (FullOrderExecution.decode bytes).map fun (message, rest) => (.fullOrderExecution message, rest)
  else if tag = 13001 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 13301 then (InstrumentStateChange.decode bytes).map fun (message, rest) => (.instrumentStateChange message, rest)
  else if tag = 13601 then (InstrumentSummary.decode bytes).map fun (message, rest) => (.instrumentSummary message, rest)
  else if tag = 13302 then (MassInstrumentStateChange.decode bytes).map fun (message, rest) => (.massInstrumentStateChange message, rest)
  else if tag = 13100 then (OrderAdd.decode bytes).map fun (message, rest) => (.orderAdd message, rest)
  else if tag = 13102 then (OrderDelete.decode bytes).map fun (message, rest) => (.orderDelete message, rest)
  else if tag = 13103 then (OrderMassDelete.decode bytes).map fun (message, rest) => (.orderMassDelete message, rest)
  else if tag = 13101 then (OrderModify.decode bytes).map fun (message, rest) => (.orderModify message, rest)
  else if tag = 13106 then (OrderModifySamePrio.decode bytes).map fun (message, rest) => (.orderModifySamePrio message, rest)
  else if tag = 13105 then (PartialOrderExecution.decode bytes).map fun (message, rest) => (.partialOrderExecution message, rest)
  else if tag = 13300 then (ProductStateChange.decode bytes).map fun (message, rest) => (.productStateChange message, rest)
  else if tag = 13600 then (ProductSummary.decode bytes).map fun (message, rest) => (.productSummary message, rest)
  else if tag = 13503 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 13602 then (SnapshotOrder.decode bytes).map fun (message, rest) => (.snapshotOrder message, rest)
  else if tag = 13203 then (TesTradeReport.decode bytes).map fun (message, rest) => (.tesTradeReport message, rest)
  else if tag = 13504 then (TopOfBook.decode bytes).map fun (message, rest) => (.topOfBook message, rest)
  else if tag = 13201 then (TradeReport.decode bytes).map fun (message, rest) => (.tradeReport message, rest)
  else if tag = 13200 then (TradeReversal.decode bytes).map fun (message, rest) => (.tradeReversal message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNum : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 4 message.msgSeqNum
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ msgSeqNum, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | addComplexInstrument inner =>
    have bound_inner := AddComplexInstrument.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | addFlexibleInstrument inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AddFlexibleInstrument.encode_length]
    omega
  | addScaledSimpleInstrument inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AddScaledSimpleInstrument.encode_length]
    omega
  | auctionBbo inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AuctionBbo.encode_length]
    omega
  | auctionClearingPrice inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AuctionClearingPrice.encode_length]
    omega
  | crossRequest inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, CrossRequest.encode_length]
    omega
  | executionSummary inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ExecutionSummary.encode_length]
    omega
  | fullOrderExecution inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, FullOrderExecution.encode_length]
    omega
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | instrumentStateChange inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, InstrumentStateChange.encode_length]
    omega
  | instrumentSummary inner =>
    have bound_inner := InstrumentSummary.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | massInstrumentStateChange inner =>
    have bound_inner := MassInstrumentStateChange.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderAdd inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderAdd.encode_length]
    omega
  | orderDelete inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderDelete.encode_length]
    omega
  | orderMassDelete inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderMassDelete.encode_length]
    omega
  | orderModify inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderModify.encode_length]
    omega
  | orderModifySamePrio inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderModifySamePrio.encode_length]
    omega
  | partialOrderExecution inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, PartialOrderExecution.encode_length]
    omega
  | productStateChange inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ProductStateChange.encode_length]
    omega
  | productSummary inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ProductSummary.encode_length]
    omega
  | quoteRequest inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, QuoteRequest.encode_length]
    omega
  | snapshotOrder inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SnapshotOrder.encode_length]
    omega
  | tesTradeReport inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TesTradeReport.encode_length]
    omega
  | topOfBook inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TopOfBook.encode_length]
    omega
  | tradeReport inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeReport.encode_length]
    omega
  | tradeReversal inner =>
    have bound_inner := TradeReversal.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  packetHeader : PacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  PacketHeader.encode message.packetHeader
    ++ encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let (packetHeader, bytes) ← PacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { packetHeader, message }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [PacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [PacketHeader.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), Option.bind_some]
  rfl

end Packet

end Omi.EurexT7EobiFbeV131
