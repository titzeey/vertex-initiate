;; VertexInitiate Supply Chain Quality Assurance Platform

;; Implements:
;;   - Dynamic Quality Nodes (DQNs) as smart contract modules
;;   - Cascading Verification Architecture
;;   - Zero-Knowledge Quality Proofs (commitment scheme)
;;   - Reputation Staking for suppliers
;;   - Time-locked Quality Escrows
;;   - Dynamic Penalty Calculations

;; -------------------------------------------------------
;; CONSTANTS
;; -------------------------------------------------------

(define-constant CONTRACT-OWNER tx-sender)

(define-constant ERR-NOT-AUTHORIZED        (err u100))
(define-constant ERR-PRODUCT-NOT-FOUND     (err u101))
(define-constant ERR-INVALID-STATUS        (err u102))
(define-constant ERR-CHECKPOINT-NOT-FOUND  (err u103))
(define-constant ERR-INSUFFICIENT-STAKE    (err u104))
(define-constant ERR-ESCROW-LOCKED         (err u105))
(define-constant ERR-ALREADY-REGISTERED    (err u106))
(define-constant ERR-INVALID-SCORE         (err u107))
(define-constant ERR-DISPUTE-NOT-FOUND     (err u108))
(define-constant ERR-ALREADY-VOTED         (err u109))

;; Product status codes
(define-constant STATUS-PENDING     u0)
(define-constant STATUS-IN-TRANSIT  u1)
(define-constant STATUS-VERIFIED    u2)
(define-constant STATUS-FLAGGED     u3)
(define-constant STATUS-RELEASED    u4)
(define-constant STATUS-DISPUTED    u5)

;; Quality score bounds (0-100)
(define-constant MIN-QUALITY-SCORE u0)
(define-constant MAX-QUALITY-SCORE u100)

;; Minimum stake required per product (in microstacks)
(define-constant BASE-STAKE-AMOUNT u1000000)

;; Penalty tiers (percentage of stake to slash, in basis points)
(define-constant PENALTY-TIER-1 u500)   ;; 5%   - minor anomaly
(define-constant PENALTY-TIER-2 u1500)  ;; 15%  - moderate anomaly
(define-constant PENALTY-TIER-3 u4000)  ;; 40%  - severe anomaly

;; Escrow lock duration (in blocks, ~144 blocks/day on Stacks)
(define-constant ESCROW-LOCK-BLOCKS u1440)  ;; ~10 days

;; Consensus threshold for dispute resolution (out of 10 votes)
(define-constant CONSENSUS-THRESHOLD u6)

;; -------------------------------------------------------
;; DATA MAPS AND VARS
;; -------------------------------------------------------

;; Tracks the next available product ID
(define-data-var next-product-id uint u1)

;; Tracks the next available dispute ID
(define-data-var next-dispute-id uint u1)

;; Registered suppliers
;; supplier-principal -> { name, reputation-score, total-stake, active }
(define-map suppliers
  principal
  {
    name:             (string-ascii 64),
    reputation-score: uint,
    total-stake:      uint,
    active:           bool
  }
)

;; Registered validators (authorized quality inspectors / oracles)
(define-map validators
  principal
  { active: bool, validated-count: uint }
)

;; Product registry
;; product-id -> product-data
(define-map products
  uint
  {
    supplier:         principal,
    batch-id:         (string-ascii 32),
    category:         (string-ascii 32),
    jurisdiction:     (string-ascii 16),
    status:           uint,
    quality-score:    uint,
    anomaly-count:    uint,
    escrow-amount:    uint,
    escrow-unlock-at: uint,
    created-at:       uint,
    updated-at:       uint
  }
)

;; Quality checkpoints per product
;; { product-id, checkpoint-index } -> checkpoint-data
(define-map quality-checkpoints
  { product-id: uint, index: uint }
  {
    validator:   principal,
    location:    (string-ascii 64),
    score:       uint,
    passed:      bool,
    anomaly:     bool,
    notes:       (string-ascii 128),
    verified-at: uint
  }
)

;; Checkpoint counters per product
(define-map checkpoint-counts uint uint)

;; Zero-Knowledge Quality Proofs (commitment scheme)
;; Supplier commits hash(process-data || salt) off-chain; we store the commitment
(define-map zk-quality-commitments
  { product-id: uint, supplier: principal }
  {
    commitment: (buff 32),  ;; keccak/sha256 commitment hash
    revealed:   bool,
    verified:   bool
  }
)

;; Supplier stakes per product
(define-map product-stakes
  { product-id: uint, supplier: principal }
  { amount: uint, slashed: uint }
)

;; Dispute registry
(define-map disputes
  uint
  {
    product-id:   uint,
    initiator:    principal,
    reason:       (string-ascii 128),
    vote-yes:     uint,
    vote-no:      uint,
    resolved:     bool,
    outcome:      bool,
    created-at:   uint
  }
)

;; Prevents double-voting in disputes
(define-map dispute-votes
  { dispute-id: uint, voter: principal }
  bool
)

;; -------------------------------------------------------
;; PRIVATE HELPERS
;; -------------------------------------------------------

;; Check if caller is the contract owner
(define-private (is-owner)
  (is-eq tx-sender CONTRACT-OWNER)
)

;; Check if caller is a registered, active supplier
(define-private (is-active-supplier (who principal))
  (match (map-get? suppliers who)
    supplier-data (get active supplier-data)
    false
  )
)

;; Check if caller is a registered, active validator
(define-private (is-active-validator (who principal))
  (match (map-get? validators who)
    v (get active v)
    false
  )
)

;; Compute dynamic penalty amount based on tier
(define-private (calc-penalty (stake-amount uint) (tier uint))
  (if (is-eq tier u1)
    (/ (* stake-amount PENALTY-TIER-1) u10000)
    (if (is-eq tier u2)
      (/ (* stake-amount PENALTY-TIER-2) u10000)
      (/ (* stake-amount PENALTY-TIER-3) u10000)
    )
  )
)

;; Determine penalty tier from anomaly count
(define-private (anomaly-count-to-tier (count uint))
  (if (< count u2)
    u1
    (if (< count u4)
      u2
      u3
    )
  )
)

;; Increment checkpoint counter for a product
(define-private (increment-checkpoint-count (product-id uint))
  (let ((current (default-to u0 (map-get? checkpoint-counts product-id))))
    (map-set checkpoint-counts product-id (+ current u1))
    (+ current u1)
  )
)

;; -------------------------------------------------------
;; ADMIN FUNCTIONS
;; -------------------------------------------------------

;; Register a new validator (oracle / quality inspector)
(define-public (register-validator (validator-principal principal))
  (begin
    (asserts! (is-owner) ERR-NOT-AUTHORIZED)
    (asserts!
      (is-none (map-get? validators validator-principal))
      ERR-ALREADY-REGISTERED
    )
    (map-set validators
      validator-principal
      { active: true, validated-count: u0 }
    )
    (ok true)
  )
)

;; Deactivate a validator
(define-public (deactivate-validator (validator-principal principal))
  (begin
    (asserts! (is-owner) ERR-NOT-AUTHORIZED)
    (match (map-get? validators validator-principal)
      v (begin
          (map-set validators
            validator-principal
            (merge v { active: false })
          )
          (ok true)
        )
      ERR-NOT-AUTHORIZED
    )
  )
)

;; -------------------------------------------------------
;; SUPPLIER FUNCTIONS
;; -------------------------------------------------------

;; Register as a new supplier
(define-public (register-supplier (name (string-ascii 64)))
  (begin
    (asserts!
      (is-none (map-get? suppliers tx-sender))
      ERR-ALREADY-REGISTERED
    )
    (map-set suppliers
      tx-sender
      {
        name:             name,
        reputation-score: u80,  ;; default starting reputation
        total-stake:      u0,
        active:           true
      }
    )
    (ok true)
  )
)

;; Register a new product and stake tokens into escrow
(define-public (register-product
    (batch-id      (string-ascii 32))
    (category      (string-ascii 32))
    (jurisdiction  (string-ascii 16))
    (escrow-amount uint)
  )
  (let
    (
      (product-id  (var-get next-product-id))
      (supplier    tx-sender)
    )
    (asserts! (is-active-supplier supplier) ERR-NOT-AUTHORIZED)
    (asserts! (>= escrow-amount BASE-STAKE-AMOUNT) ERR-INSUFFICIENT-STAKE)

    ;; Transfer escrow amount to contract
    (try! (stx-transfer? escrow-amount supplier (as-contract tx-sender)))

    ;; Record product
    (map-set products product-id
      {
        supplier:         supplier,
        batch-id:         batch-id,
        category:         category,
        jurisdiction:     jurisdiction,
        status:           STATUS-PENDING,
        quality-score:    u100,
        anomaly-count:    u0,
        escrow-amount:    escrow-amount,
        escrow-unlock-at: (+ block-height ESCROW-LOCK-BLOCKS),
        created-at:       block-height,
        updated-at:       block-height
      }
    )

    ;; Record supplier stake
    (map-set product-stakes
      { product-id: product-id, supplier: supplier }
      { amount: escrow-amount, slashed: u0 }
    )

    ;; Update supplier total-stake
    (match (map-get? suppliers supplier)
      s (map-set suppliers supplier
          (merge s { total-stake: (+ (get total-stake s) escrow-amount) })
        )
      false
    )

    ;; Advance product ID counter
    (var-set next-product-id (+ product-id u1))
    (ok product-id)
  )
)

;; Submit a Zero-Knowledge Quality Proof commitment
;; The supplier commits sha256(process-data || salt) before revealing
(define-public (submit-zk-commitment
    (product-id uint)
    (commitment  (buff 32))
  )
  (let ((product (unwrap! (map-get? products product-id) ERR-PRODUCT-NOT-FOUND)))
    (asserts! (is-eq tx-sender (get supplier product)) ERR-NOT-AUTHORIZED)
    (map-set zk-quality-commitments
      { product-id: product-id, supplier: tx-sender }
      { commitment: commitment, revealed: false, verified: false }
    )
    (ok true)
  )
)

;; Reveal ZK commitment (supply preimage for on-chain verification)
;; In production, actual ZK proof verification would be handled off-chain
;; or via a dedicated verifier contract; here we verify the hash preimage.
(define-public (reveal-zk-commitment
    (product-id uint)
    (preimage    (buff 128))
  )
  (let
    (
      (key        { product-id: product-id, supplier: tx-sender })
      (commitment-data
        (unwrap! (map-get? zk-quality-commitments key) ERR-PRODUCT-NOT-FOUND))
    )
    (asserts! (not (get revealed commitment-data)) ERR-INVALID-STATUS)
    ;; Verify sha256(preimage) matches stored commitment
    (asserts!
      (is-eq (sha256 preimage) (get commitment commitment-data))
      ERR-NOT-AUTHORIZED
    )
    (map-set zk-quality-commitments key
      (merge commitment-data { revealed: true, verified: true })
    )
    (ok true)
  )
)

;; -------------------------------------------------------
;; VALIDATOR / CHECKPOINT FUNCTIONS
;; -------------------------------------------------------

;; Record a quality checkpoint for a product (Dynamic Quality Node update)
;; Implements Cascading Verification: anomalies escalate status to FLAGGED
(define-public (record-checkpoint
    (product-id uint)
    (location   (string-ascii 64))
    (score      uint)
    (anomaly    bool)
    (notes      (string-ascii 128))
  )
  (let
    (
      (product  (unwrap! (map-get? products product-id) ERR-PRODUCT-NOT-FOUND))
      (idx      (increment-checkpoint-count product-id))
    )
    (asserts! (is-active-validator tx-sender) ERR-NOT-AUTHORIZED)
    (asserts! (<= score MAX-QUALITY-SCORE) ERR-INVALID-SCORE)
    (asserts!
      (or
        (is-eq (get status product) STATUS-PENDING)
        (is-eq (get status product) STATUS-IN-TRANSIT)
        (is-eq (get status product) STATUS-FLAGGED)
      )
      ERR-INVALID-STATUS
    )

    ;; Store checkpoint
    (map-set quality-checkpoints
      { product-id: product-id, index: idx }
      {
        validator:   tx-sender,
        location:    location,
        score:       score,
        passed:      (>= score u70),
        anomaly:     anomaly,
        notes:       notes,
        verified-at: block-height
      }
    )

    ;; Update validator stats
    (match (map-get? validators tx-sender)
      v (map-set validators tx-sender
          (merge v { validated-count: (+ (get validated-count v) u1) })
        )
      false
    )

    ;; Cascading Verification: update product status and quality score
    (let
      (
        (new-anomaly-count
          (if anomaly
            (+ (get anomaly-count product) u1)
            (get anomaly-count product)
          )
        )
        ;; Weighted average of current score and new checkpoint score
        (new-quality-score
          (/ (+ (get quality-score product) score) u2)
        )
        (new-status
          (if anomaly STATUS-FLAGGED STATUS-IN-TRANSIT)
        )
      )
      (map-set products product-id
        (merge product
          {
            status:        new-status,
            quality-score: new-quality-score,
            anomaly-count: new-anomaly-count,
            updated-at:    block-height
          }
        )
      )

      ;; Apply dynamic penalty if anomaly detected
      (if anomaly
        (apply-penalty product-id (get supplier product) new-anomaly-count)
        (ok true)
      )
    )
  )
)

;; Mark a product as verified and ready for escrow release
(define-public (verify-product (product-id uint))
  (let ((product (unwrap! (map-get? products product-id) ERR-PRODUCT-NOT-FOUND)))
    (asserts! (is-active-validator tx-sender) ERR-NOT-AUTHORIZED)
    (asserts! (is-eq (get status product) STATUS-IN-TRANSIT) ERR-INVALID-STATUS)
    (asserts! (>= (get quality-score product) u70) ERR-INVALID-SCORE)
    (map-set products product-id
      (merge product { status: STATUS-VERIFIED, updated-at: block-height })
    )
    (ok true)
  )
)

;; -------------------------------------------------------
;; PENALTY (DYNAMIC CALCULATION)
;; -------------------------------------------------------

;; Internal: slash a portion of the supplier stake based on anomaly severity
(define-private (apply-penalty
    (product-id    uint)
    (supplier      principal)
    (anomaly-count uint)
  )
  (let
    (
      (stake-key  { product-id: product-id, supplier: supplier })
      (stake-data (default-to { amount: u0, slashed: u0 }
                    (map-get? product-stakes stake-key)))
      (tier       (anomaly-count-to-tier anomaly-count))
      (penalty    (calc-penalty (get amount stake-data) tier))
      (new-slashed (+ (get slashed stake-data) penalty))
    )
    (map-set product-stakes stake-key
      (merge stake-data { slashed: new-slashed })
    )
    ;; Update supplier reputation score (decrease by tier * 2)
    (match (map-get? suppliers supplier)
      s (map-set suppliers supplier
          (merge s {
            reputation-score:
              (if (> (get reputation-score s) (* tier u2))
                (- (get reputation-score s) (* tier u2))
                u0
              )
          })
        )
      false
    )
    (ok true)
  )
)

;; -------------------------------------------------------
;; ESCROW RELEASE
;; -------------------------------------------------------

;; Release escrow to supplier after successful verification and lock period
(define-public (release-escrow (product-id uint))
  (let
    (
      (product  (unwrap! (map-get? products product-id) ERR-PRODUCT-NOT-FOUND))
      (supplier (get supplier product))
    )
    (asserts! (is-eq tx-sender supplier) ERR-NOT-AUTHORIZED)
    (asserts! (is-eq (get status product) STATUS-VERIFIED) ERR-INVALID-STATUS)
    (asserts!
      (>= block-height (get escrow-unlock-at product))
      ERR-ESCROW-LOCKED
    )

    (let
      (
        (stake-data  (default-to { amount: u0, slashed: u0 }
                       (map-get? product-stakes
                         { product-id: product-id, supplier: supplier })))
        (payout      (- (get amount stake-data) (get slashed stake-data)))
      )
      ;; Transfer remaining escrow back to supplier
      (try!
        (as-contract
          (stx-transfer? payout tx-sender supplier)
        )
      )
      (map-set products product-id
        (merge product { status: STATUS-RELEASED, updated-at: block-height })
      )
      (ok payout)
    )
  )
)

;; -------------------------------------------------------
;; DISPUTE RESOLUTION (MULTI-STAKEHOLDER CONSENSUS)
;; -------------------------------------------------------

;; Initiate a dispute on a flagged or verified product
(define-public (initiate-dispute
    (product-id uint)
    (reason     (string-ascii 128))
  )
  (let
    (
      (product    (unwrap! (map-get? products product-id) ERR-PRODUCT-NOT-FOUND))
      (dispute-id (var-get next-dispute-id))
    )
    (asserts!
      (or
        (is-eq (get status product) STATUS-FLAGGED)
        (is-eq (get status product) STATUS-VERIFIED)
      )
      ERR-INVALID-STATUS
    )
    (map-set disputes dispute-id
      {
        product-id: product-id,
        initiator:  tx-sender,
        reason:     reason,
        vote-yes:   u0,
        vote-no:    u0,
        resolved:   false,
        outcome:    false,
        created-at: block-height
      }
    )
    (map-set products product-id
      (merge product { status: STATUS-DISPUTED, updated-at: block-height })
    )
    (var-set next-dispute-id (+ dispute-id u1))
    (ok dispute-id)
  )
)

;; Cast a vote on an active dispute (validators only)
(define-public (vote-on-dispute (dispute-id uint) (vote bool))
  (let
    (
      (dispute
        (unwrap! (map-get? disputes dispute-id) ERR-DISPUTE-NOT-FOUND))
      (vote-key { dispute-id: dispute-id, voter: tx-sender })
    )
    (asserts! (is-active-validator tx-sender) ERR-NOT-AUTHORIZED)
    (asserts! (not (get resolved dispute)) ERR-INVALID-STATUS)
    (asserts! (is-none (map-get? dispute-votes vote-key)) ERR-ALREADY-VOTED)

    (map-set dispute-votes vote-key true)
    (map-set disputes dispute-id
      (merge dispute {
        vote-yes: (if vote (+ (get vote-yes dispute) u1) (get vote-yes dispute)),
        vote-no:  (if (not vote) (+ (get vote-no dispute) u1) (get vote-no dispute))
      })
    )
    (ok true)
  )
)

;; Resolve a dispute once enough votes have been cast
;; Outcome true  = product quality confirmed (restore to VERIFIED)
;; Outcome false = quality rejected           (remains DISPUTED / penalized)
(define-public (resolve-dispute (dispute-id uint))
  (let
    (
      (dispute
        (unwrap! (map-get? disputes dispute-id) ERR-DISPUTE-NOT-FOUND))
      (total-votes (+ (get vote-yes dispute) (get vote-no dispute)))
      (outcome     (>= (get vote-yes dispute) CONSENSUS-THRESHOLD))
      (product
        (unwrap!
          (map-get? products (get product-id dispute))
          ERR-PRODUCT-NOT-FOUND))
    )
    (asserts! (is-owner) ERR-NOT-AUTHORIZED)
    (asserts! (not (get resolved dispute)) ERR-INVALID-STATUS)
    (asserts! (>= total-votes CONSENSUS-THRESHOLD) ERR-INVALID-STATUS)

    (map-set disputes dispute-id
      (merge dispute { resolved: true, outcome: outcome })
    )
    ;; Update product status based on consensus outcome
    (map-set products (get product-id dispute)
      (merge product {
        status:     (if outcome STATUS-VERIFIED STATUS-FLAGGED),
        updated-at: block-height
      })
    )
    (ok outcome)
  )
)

;; -------------------------------------------------------
;; READ-ONLY FUNCTIONS
;; -------------------------------------------------------

;; Get full product details
(define-read-only (get-product (product-id uint))
  (map-get? products product-id)
)

;; Get a specific quality checkpoint
(define-read-only (get-checkpoint (product-id uint) (index uint))
  (map-get? quality-checkpoints { product-id: product-id, index: index })
)

;; Get total checkpoint count for a product
(define-read-only (get-checkpoint-count (product-id uint))
  (default-to u0 (map-get? checkpoint-counts product-id))
)

;; Get supplier info
(define-read-only (get-supplier (supplier principal))
  (map-get? suppliers supplier)
)

;; Get validator info
(define-read-only (get-validator (validator principal))
  (map-get? validators validator)
)

;; Get stake info for a product/supplier pair
(define-read-only (get-product-stake (product-id uint) (supplier principal))
  (map-get? product-stakes { product-id: product-id, supplier: supplier })
)

;; Get ZK commitment for a product/supplier pair
(define-read-only (get-zk-commitment (product-id uint) (supplier principal))
  (map-get? zk-quality-commitments
    { product-id: product-id, supplier: supplier })
)

;; Get dispute details
(define-read-only (get-dispute (dispute-id uint))
  (map-get? disputes dispute-id)
)

;; Check if a validator has voted on a dispute
(define-read-only (has-voted (dispute-id uint) (voter principal))
  (is-some (map-get? dispute-votes { dispute-id: dispute-id, voter: voter }))
)

;; Get current product ID counter
(define-read-only (get-next-product-id)
  (var-get next-product-id)
)
