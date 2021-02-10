const assert = require("assert");
//const anchor = require("@project-serum/anchor");
const anchor = require('/home/armaniferrante/Documents/code/src/github.com/project-serum/anchor/ts');
const serumCmn = require("@project-serum/common");
const TokenInstructions = require("@project-serum/serum").TokenInstructions;
const utils = require("./utils");

describe("Lockup and Registry", () => {
  // Read the provider from the configured environmnet.
  const provider = anchor.Provider.env();

  // Configure the client to use the provider.
  anchor.setProvider(provider);

	const lockup = anchor.workspace.Lockup;
	const linear = anchor.workspace.Linear;
  const registry = anchor.workspace.Registry;

  let lockupAddress = null;
  const WHITELIST_SIZE = 10;

  let mint = null;
  let god = null;

  it("Sets up initial test state", async () => {
    const [_mint, _god] = await serumCmn.createMintAndVault(
      provider,
      new anchor.BN(1000000)
    );
    mint = _mint;
    god = _god;
  });

  it("Is initialized!", async () => {
    await lockup.state.rpc.new({
      accounts: {
        authority: provider.wallet.publicKey,
      },
    });

    lockupAddress = await lockup.state.address();
    const lockupAccount = await lockup.state();

    assert.ok(lockupAccount.authority.equals(provider.wallet.publicKey));
    assert.ok(lockupAccount.whitelist.length === WHITELIST_SIZE);
    lockupAccount.whitelist.forEach((e) => {
      assert.ok(e.programId.equals(new anchor.web3.PublicKey()));
    });
  });

  it("Deletes the default whitelisted addresses", async () => {
    const defaultEntry = { programId: new anchor.web3.PublicKey() };
    await lockup.state.rpc.whitelistDelete(defaultEntry, {
      accounts: {
        authority: provider.wallet.publicKey,
      },
    });
  });

  it("Sets a new authority", async () => {
    const newAuthority = new anchor.web3.Account();
    await lockup.state.rpc.setAuthority(newAuthority.publicKey, {
      accounts: {
        authority: provider.wallet.publicKey,
      },
    });

    let lockupAccount = await lockup.state();
    assert.ok(lockupAccount.authority.equals(newAuthority.publicKey));

    await lockup.state.rpc.setAuthority(provider.wallet.publicKey, {
      accounts: {
        authority: newAuthority.publicKey,
      },
      signers: [newAuthority],
    });

    lockupAccount = await lockup.state();
    assert.ok(lockupAccount.authority.equals(provider.wallet.publicKey));
  });

  const entries = [];

  it("Adds to the whitelist", async () => {
    const generateEntry = async () => {
      let programId = new anchor.web3.Account().publicKey;
      return {
        programId,
      };
    };

    for (let k = 0; k < WHITELIST_SIZE; k += 1) {
      entries.push(await generateEntry());
    }

    const accounts = {
      authority: provider.wallet.publicKey,
    };

    await lockup.state.rpc.whitelistAdd(entries[0], { accounts });

    let lockupAccount = await lockup.state();

    assert.ok(lockupAccount.whitelist.length === 1);
    assert.deepEqual(lockupAccount.whitelist, [entries[0]]);

    for (let k = 1; k < WHITELIST_SIZE; k += 1) {
      await lockup.state.rpc.whitelistAdd(entries[k], { accounts });
    }

    lockupAccount = await lockup.state();

    assert.deepEqual(lockupAccount.whitelist, entries);

    await assert.rejects(
      async () => {
        const e = await generateEntry();
        await lockup.state.rpc.whitelistAdd(e, { accounts });
      },
      (err) => {
        assert.equal(err.code, 106);
        assert.equal(err.msg, "Whitelist is full");
        return true;
      }
    );
  });

  it("Removes from the whitelist", async () => {
    await lockup.state.rpc.whitelistDelete(entries[0], {
      accounts: {
        authority: provider.wallet.publicKey,
      },
    });
    let lockupAccount = await lockup.state();
    assert.deepEqual(lockupAccount.whitelist, entries.slice(1));
  });


	const schedule = new anchor.web3.Account();
	const startTs = new anchor.BN(Date.now() / 1000);
	const endTs = new anchor.BN(startTs.toNumber() + 5);
	const periodCount = new anchor.BN(2);

  it('Creates a vesting schedule', async () => {
			await linear.rpc.createSchedule(startTs, endTs, periodCount, {
					accounts: {
							schedule: schedule.publicKey,
							rent: anchor.web3.SYSVAR_RENT_PUBKEY,
					},
					instructions: [
							await linear.account.schedule.createInstruction(schedule),
					],
					signers: [schedule],
			});

			const scheduleAccount = await linear.account.schedule(schedule.publicKey);

			assert.ok(scheduleAccount.startTs.eq(startTs));
			assert.ok(scheduleAccount.endTs.eq(endTs));
			assert.ok(scheduleAccount.periodCount.eq(periodCount));
	});

  const vesting = new anchor.web3.Account();
  let vestingAccount = null;
  let vestingSigner = null;

  it("Creates a vesting account", async () => {
    const beneficiary = provider.wallet.publicKey;
    const depositAmount = new anchor.BN(100);

    const vault = new anchor.web3.Account();
    let [
      _vestingSigner,
      nonce,
    ] = await anchor.web3.PublicKey.findProgramAddress(
      [vesting.publicKey.toBuffer()],
      lockup.programId
    );
    vestingSigner = _vestingSigner;

    await lockup.rpc.createVesting(
      beneficiary,
      depositAmount,
			nonce,
			{ program: linear.programId, metadata: schedule.publicKey },
      null, // Lock realizor is None.
      {
        accounts: {
          vesting: vesting.publicKey,
          vault: vault.publicKey,
          depositor: god,
          depositorAuthority: provider.wallet.publicKey,
          tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
          rent: anchor.web3.SYSVAR_RENT_PUBKEY,
          clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
        },
        signers: [vesting, vault],
        instructions: [
          await lockup.account.vesting.createInstruction(vesting),
          ...(await serumCmn.createTokenAccountInstrs(
            provider,
            vault.publicKey,
            mint,
            vestingSigner
          )),
        ],
      }
    );

    vestingAccount = await lockup.account.vesting(vesting.publicKey);

    assert.ok(vestingAccount.beneficiary.equals(provider.wallet.publicKey));
    assert.ok(vestingAccount.mint.equals(mint));
    assert.ok(vestingAccount.grantor.equals(provider.wallet.publicKey));
    assert.ok(vestingAccount.outstanding.eq(depositAmount));
    assert.ok(vestingAccount.startBalance.eq(depositAmount));
    assert.ok(vestingAccount.whitelistOwned.eq(new anchor.BN(0)));
    assert.equal(vestingAccount.nonce, nonce);
		assert.ok(vestingAccount.createdTs.gt(new anchor.BN(0)));
    assert.ok(vestingAccount.realizor === null);
  });

  it("Fails to withdraw from a vesting account before vesting", async () => {
    await assert.rejects(
      async () => {
        await lockup.rpc.withdraw(new anchor.BN(100), {
          accounts: {
            vesting: vesting.publicKey,
            beneficiary: provider.wallet.publicKey,
            token: god,
            vault: vestingAccount.vault,
            vestingSigner: vestingSigner,
            tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
						clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
						scheduleProgram: linear.programId,
						scheduleMetadata: schedule.publicKey,
          },
        });
      },
				(err) => {
						console.log('err', err);
        assert.equal(err.code, 105);
        assert.equal(err.msg, "Insufficient withdrawal balance.");
        return true;
      }
    );
  });

  it("Waits for a vesting period to pass", async () => {
    await serumCmn.sleep(10 * 1000);
  });

  it("Withdraws from the vesting account", async () => {
    const token = await serumCmn.createTokenAccount(
      provider,
      mint,
      provider.wallet.publicKey
    );

    await lockup.rpc.withdraw(new anchor.BN(100), {
      accounts: {
        vesting: vesting.publicKey,
        beneficiary: provider.wallet.publicKey,
        token,
        vault: vestingAccount.vault,
        vestingSigner,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
				clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
				scheduleProgram: linear.programId,
				scheduleMetadata: schedule.publicKey,
      },
    });

    vestingAccount = await lockup.account.vesting(vesting.publicKey);
    assert.ok(vestingAccount.outstanding.eq(new anchor.BN(0)));

    const vaultAccount = await serumCmn.getTokenAccount(
      provider,
      vestingAccount.vault
    );
    assert.ok(vaultAccount.amount.eq(new anchor.BN(0)));

    const tokenAccount = await serumCmn.getTokenAccount(provider, token);
    assert.ok(tokenAccount.amount.eq(new anchor.BN(100)));
  });

  const registrar = new anchor.web3.Account();
  const rewardQ = new anchor.web3.Account();
  const withdrawalTimelock = new anchor.BN(4);
  const stakeRate = new anchor.BN(2);
  const rewardQLen = 170;
  let registrarAccount = null;
  let registrarSigner = null;
  let nonce = null;
  let poolMint = null;

  it("Creates registry genesis", async () => {
    const [
      _registrarSigner,
      _nonce,
    ] = await anchor.web3.PublicKey.findProgramAddress(
      [registrar.publicKey.toBuffer()],
      registry.programId
    );
    registrarSigner = _registrarSigner;
    nonce = _nonce;
    poolMint = await serumCmn.createMint(provider, registrarSigner);
  });

  it("Initializes registry's global state", async () => {
    await registry.state.rpc.new({
      accounts: { lockupProgram: lockup.programId },
    });

    const state = await registry.state();
    assert.ok(state.lockupProgram.equals(lockup.programId));

    // Should not allow a second initializatoin.
    await assert.rejects(
      async () => {
        await registry.state.rpc.new(lockup.programId);
      },
      (err) => {
        return true;
      }
    );
  });

  it("Initializes the registrar", async () => {
    await registry.rpc.initialize(
      mint,
      provider.wallet.publicKey,
      nonce,
      withdrawalTimelock,
      stakeRate,
      rewardQLen,
      {
        accounts: {
          registrar: registrar.publicKey,
          poolMint,
          rewardEventQ: rewardQ.publicKey,
          rent: anchor.web3.SYSVAR_RENT_PUBKEY,
        },
        signers: [registrar, rewardQ],
        instructions: [
          await registry.account.registrar.createInstruction(registrar),
          await registry.account.rewardQueue.createInstruction(rewardQ, 8250),
        ],
      }
    );

    registrarAccount = await registry.account.registrar(registrar.publicKey);

    assert.ok(registrarAccount.authority.equals(provider.wallet.publicKey));
    assert.equal(registrarAccount.nonce, nonce);
    assert.ok(registrarAccount.mint.equals(mint));
    assert.ok(registrarAccount.poolMint.equals(poolMint));
    assert.ok(registrarAccount.stakeRate.eq(stakeRate));
    assert.ok(registrarAccount.rewardEventQ.equals(rewardQ.publicKey));
    assert.ok(registrarAccount.withdrawalTimelock.eq(withdrawalTimelock));
  });

  const member = new anchor.web3.Account();
  let memberAccount = null;
  let memberSigner = null;
  let balances = null;
  let balancesLocked = null;

  it("Creates a member", async () => {
    const [
      _memberSigner,
      nonce,
    ] = await anchor.web3.PublicKey.findProgramAddress(
      [registrar.publicKey.toBuffer(), member.publicKey.toBuffer()],
      registry.programId
    );
    memberSigner = _memberSigner;

    const [mainTx, _balances] = await utils.createBalanceSandbox(
      provider,
      registrarAccount,
      memberSigner
    );
    const [lockedTx, _balancesLocked] = await utils.createBalanceSandbox(
      provider,
      registrarAccount,
      memberSigner
    );

    balances = _balances;
    balancesLocked = _balancesLocked;

    const tx = registry.transaction.createMember(nonce, {
      accounts: {
        registrar: registrar.publicKey,
        member: member.publicKey,
        beneficiary: provider.wallet.publicKey,
        memberSigner,
        balances,
        balancesLocked,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
        rent: anchor.web3.SYSVAR_RENT_PUBKEY,
      },
      instructions: [await registry.account.member.createInstruction(member)],
    });

    const signers = [member, provider.wallet.payer];

    const allTxs = [mainTx, lockedTx, { tx, signers }];

    let txSigs = await provider.sendAll(allTxs);

    memberAccount = await registry.account.member(member.publicKey);

    assert.ok(memberAccount.registrar.equals(registrar.publicKey));
    assert.ok(memberAccount.beneficiary.equals(provider.wallet.publicKey));
    assert.ok(memberAccount.metadata.equals(new anchor.web3.PublicKey()));
    assert.equal(
      JSON.stringify(memberAccount.balances),
      JSON.stringify(balances)
    );
    assert.equal(
      JSON.stringify(memberAccount.balancesLocked),
      JSON.stringify(balancesLocked)
    );
    assert.ok(memberAccount.rewardsCursor === 0);
    assert.ok(memberAccount.lastStakeTs.eq(new anchor.BN(0)));
  });

  it("Deposits (unlocked) to a member", async () => {
    const depositAmount = new anchor.BN(120);
    await registry.rpc.deposit(depositAmount, {
      accounts: {
        depositor: god,
        depositorAuthority: provider.wallet.publicKey,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
        vault: memberAccount.balances.vault,
        beneficiary: provider.wallet.publicKey,
        member: member.publicKey,
      },
    });

    const memberVault = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vault
    );
    assert.ok(memberVault.amount.eq(depositAmount));
  });

  it("Stakes to a member (unlocked)", async () => {
    const stakeAmount = new anchor.BN(10);
    await registry.rpc.stake(stakeAmount, false, {
      accounts: {
        // Stake instance.
        registrar: registrar.publicKey,
        rewardEventQ: rewardQ.publicKey,
        poolMint,
        // Member.
        member: member.publicKey,
        beneficiary: provider.wallet.publicKey,
        balances,
        balancesLocked,
        // Program signers.
        memberSigner,
        registrarSigner,
        // Misc.
        clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
      },
    });

    const vault = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vault
    );
    const vaultStake = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vaultStake
    );
    const spt = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.spt
    );

    assert.ok(vault.amount.eq(new anchor.BN(100)));
    assert.ok(vaultStake.amount.eq(new anchor.BN(20)));
    assert.ok(spt.amount.eq(new anchor.BN(10)));
  });

  const unlockedVendor = new anchor.web3.Account();
  const unlockedVendorVault = new anchor.web3.Account();
  let unlockedVendorSigner = null;

  it("Drops an unlocked reward", async () => {
    const rewardKind = {
      unlocked: {},
    };
    const rewardAmount = new anchor.BN(200);
    const expiry = new anchor.BN(Date.now() / 1000 + 5);
    const [
      _vendorSigner,
      nonce,
    ] = await anchor.web3.PublicKey.findProgramAddress(
      [registrar.publicKey.toBuffer(), unlockedVendor.publicKey.toBuffer()],
      registry.programId
    );
    unlockedVendorSigner = _vendorSigner;

    await registry.rpc.dropReward(
      rewardKind,
      rewardAmount,
      expiry,
      provider.wallet.publicKey,
      nonce,
      {
        accounts: {
          registrar: registrar.publicKey,
          rewardEventQ: rewardQ.publicKey,
          poolMint,

          vendor: unlockedVendor.publicKey,
          vendorVault: unlockedVendorVault.publicKey,

          depositor: god,
          depositorAuthority: provider.wallet.publicKey,

          tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
          clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
          rent: anchor.web3.SYSVAR_RENT_PUBKEY,
        },
        signers: [unlockedVendorVault, unlockedVendor],
        instructions: [
          ...(await serumCmn.createTokenAccountInstrs(
            provider,
            unlockedVendorVault.publicKey,
            mint,
            unlockedVendorSigner
          )),
          await registry.account.rewardVendor.createInstruction(unlockedVendor),
        ],
      }
    );

    const vendorAccount = await registry.account.rewardVendor(
      unlockedVendor.publicKey
    );

    assert.ok(vendorAccount.registrar.equals(registrar.publicKey));
    assert.ok(vendorAccount.vault.equals(unlockedVendorVault.publicKey));
    assert.ok(vendorAccount.nonce === nonce);
    assert.ok(vendorAccount.poolTokenSupply.eq(new anchor.BN(10)));
    assert.ok(vendorAccount.expiryTs.eq(expiry));
    assert.ok(vendorAccount.expiryReceiver.equals(provider.wallet.publicKey));
    assert.ok(vendorAccount.total.eq(rewardAmount));
    assert.ok(vendorAccount.expired === false);
    assert.ok(vendorAccount.rewardEventQCursor === 0);
    assert.deepEqual(vendorAccount.kind, rewardKind);

    const rewardQAccount = await registry.account.rewardQueue(
      rewardQ.publicKey
    );
    assert.ok(rewardQAccount.head === 1);
    assert.ok(rewardQAccount.tail === 0);
    const e = rewardQAccount.events[0];
    assert.ok(e.vendor.equals(unlockedVendor.publicKey));
    assert.equal(e.locked, false);
  });

  it("Collects an unlocked reward", async () => {
    const token = await serumCmn.createTokenAccount(
      provider,
      mint,
      provider.wallet.publicKey
    );
    await registry.rpc.claimReward({
      accounts: {
        to: token,
        cmn: {
          registrar: registrar.publicKey,

          member: member.publicKey,
          beneficiary: provider.wallet.publicKey,
          balances,
          balancesLocked,

          vendor: unlockedVendor.publicKey,
          vault: unlockedVendorVault.publicKey,
          vendorSigner: unlockedVendorSigner,

          tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
          clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
        },
      },
    });

    let tokenAccount = await serumCmn.getTokenAccount(provider, token);
    assert.ok(tokenAccount.amount.eq(new anchor.BN(200)));

    const memberAccount = await registry.account.member(member.publicKey);
    assert.ok(memberAccount.rewardsCursor == 1);
  });

  const lockedVendor = new anchor.web3.Account();
  const lockedVendorVault = new anchor.web3.Account();
  let lockedVendorSigner = null;
  let lockedRewardAmount = null;
  let lockedRewardKind = null;

  it("Drops a locked reward", async () => {
    lockedRewardKind = {
      locked: {
        endTs: new anchor.BN(Date.now() / 1000 + 6),
        periodCount: new anchor.BN(2),
        schedule: null, // Custom vesting schedule: None.
      },
    };
    lockedRewardAmount = new anchor.BN(200);
    const expiry = new anchor.BN(Date.now() / 1000 + 5);
    const [
      _vendorSigner,
      nonce,
    ] = await anchor.web3.PublicKey.findProgramAddress(
      [registrar.publicKey.toBuffer(), lockedVendor.publicKey.toBuffer()],
      registry.programId
    );
    lockedVendorSigner = _vendorSigner;

    await registry.rpc.dropReward(
      lockedRewardKind,
      lockedRewardAmount,
      expiry,
      provider.wallet.publicKey,
      nonce,
      {
        accounts: {
          registrar: registrar.publicKey,
          rewardEventQ: rewardQ.publicKey,
          poolMint,

          vendor: lockedVendor.publicKey,
          vendorVault: lockedVendorVault.publicKey,

          depositor: god,
          depositorAuthority: provider.wallet.publicKey,

          tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
          clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
          rent: anchor.web3.SYSVAR_RENT_PUBKEY,
        },
        signers: [lockedVendorVault, lockedVendor],
        instructions: [
          ...(await serumCmn.createTokenAccountInstrs(
            provider,
            lockedVendorVault.publicKey,
            mint,
            lockedVendorSigner
          )),
          await registry.account.rewardVendor.createInstruction(lockedVendor),
        ],
      }
    );

    const vendorAccount = await registry.account.rewardVendor(
      lockedVendor.publicKey
    );

    assert.ok(vendorAccount.registrar.equals(registrar.publicKey));
    assert.ok(vendorAccount.vault.equals(lockedVendorVault.publicKey));
    assert.ok(vendorAccount.nonce === nonce);
    assert.ok(vendorAccount.poolTokenSupply.eq(new anchor.BN(10)));
    assert.ok(vendorAccount.expiryTs.eq(expiry));
    assert.ok(vendorAccount.expiryReceiver.equals(provider.wallet.publicKey));
    assert.ok(vendorAccount.total.eq(lockedRewardAmount));
    assert.ok(vendorAccount.expired === false);
    assert.ok(vendorAccount.rewardEventQCursor === 1);
    assert.equal(
      JSON.stringify(vendorAccount.kind),
      JSON.stringify(lockedRewardKind)
    );

    const rewardQAccount = await registry.account.rewardQueue(
      rewardQ.publicKey
    );
    assert.ok(rewardQAccount.head === 2);
    assert.ok(rewardQAccount.tail === 0);
    const e = rewardQAccount.events[1];
    assert.ok(e.vendor.equals(lockedVendor.publicKey));
    assert.ok(e.locked === true);
  });

  let vendoredVesting = null;
  let vendoredVestingVault = null;
  let vendoredVestingSigner = null;

  it("Claims a locked reward", async () => {
    vendoredVesting = new anchor.web3.Account();
    vendoredVestingVault = new anchor.web3.Account();
    let [
      _vendoredVestingSigner,
      nonce,
    ] = await anchor.web3.PublicKey.findProgramAddress(
      [vendoredVesting.publicKey.toBuffer()],
      lockup.programId
    );
    vendoredVestingSigner = _vendoredVestingSigner;
    const remainingAccounts = lockup.instruction.createVesting
      .accounts({
        vesting: vendoredVesting.publicKey,
        vault: vendoredVestingVault.publicKey,
        depositor: lockedVendorVault.publicKey,
        depositorAuthority: lockedVendorSigner,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
        rent: anchor.web3.SYSVAR_RENT_PUBKEY,
        clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
      })
      // Change the signer status on the vendor signer since it's signed by the program, not the
      // client.
      .map((meta) =>
        meta.pubkey === lockedVendorSigner ? { ...meta, isSigner: false } : meta
      );

    await registry.rpc.claimRewardLocked(nonce, {
      accounts: {
        registry: await registry.state.address(),
        lockupProgram: lockup.programId,
        cmn: {
          registrar: registrar.publicKey,

          member: member.publicKey,
          beneficiary: provider.wallet.publicKey,
          balances,
          balancesLocked,

          vendor: lockedVendor.publicKey,
          vault: lockedVendorVault.publicKey,
          vendorSigner: lockedVendorSigner,

          tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
          clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
        },
      },
      remainingAccounts,
      signers: [vendoredVesting, vendoredVestingVault],
      instructions: [
        await lockup.account.vesting.createInstruction(vendoredVesting),
        ...(await serumCmn.createTokenAccountInstrs(
          provider,
          vendoredVestingVault.publicKey,
          mint,
          vendoredVestingSigner
        )),
      ],
    });

    const lockupAccount = await lockup.account.vesting(
      vendoredVesting.publicKey
    );

    assert.ok(lockupAccount.beneficiary.equals(provider.wallet.publicKey));
    assert.ok(lockupAccount.mint.equals(mint));
    assert.ok(lockupAccount.vault.equals(vendoredVestingVault.publicKey));
    assert.ok(lockupAccount.outstanding.eq(lockedRewardAmount));
    assert.ok(lockupAccount.startBalance.eq(lockedRewardAmount));
    assert.ok(lockupAccount.endTs.eq(lockedRewardKind.locked.endTs));
    assert.ok(
      lockupAccount.periodCount.eq(lockedRewardKind.locked.periodCount)
    );
    assert.ok(lockupAccount.whitelistOwned.eq(new anchor.BN(0)));
    assert.ok(lockupAccount.realizor.program.equals(registry.programId));
    assert.ok(lockupAccount.realizor.metadata.equals(member.publicKey));
  });

  it("Waits for the lockup period to pass", async () => {
    await serumCmn.sleep(10 * 1000);
  });

  it("Should fail to unlock an unrealized lockup reward", async () => {
    const token = await serumCmn.createTokenAccount(
      provider,
      mint,
      provider.wallet.publicKey
    );
    await assert.rejects(
      async () => {
        const withdrawAmount = new anchor.BN(10);
        await lockup.rpc.withdraw(withdrawAmount, {
          accounts: {
            vesting: vendoredVesting.publicKey,
            beneficiary: provider.wallet.publicKey,
            token,
            vault: vendoredVestingVault.publicKey,
            vestingSigner: vendoredVestingSigner,
            tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
            clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
          },
          // TODO: trait methods generated on the client. Until then, we need to manually
          //       specify the account metas here.
          remainingAccounts: [
            { pubkey: registry.programId, isWritable: false, isSigner: false },
            { pubkey: member.publicKey, isWritable: false, isSigner: false },
            { pubkey: balances.spt, isWritable: false, isSigner: false },
            { pubkey: balancesLocked.spt, isWritable: false, isSigner: false },
          ],
        });
      },
      (err) => {
        // Solana doesn't propagate errors across CPI. So we receive the registry's error code,
        // not the lockup's.
        const errorCode = "custom program error: 0x78";
        assert.ok(err.toString().split(errorCode).length === 2);
        return true;
      }
    );
  });

  const pendingWithdrawal = new anchor.web3.Account();

  it("Unstakes (unlocked)", async () => {
    const unstakeAmount = new anchor.BN(10);

    await registry.rpc.startUnstake(unstakeAmount, false, {
      accounts: {
        registrar: registrar.publicKey,
        rewardEventQ: rewardQ.publicKey,
        poolMint,

        pendingWithdrawal: pendingWithdrawal.publicKey,
        member: member.publicKey,
        beneficiary: provider.wallet.publicKey,
        balances,
        balancesLocked,

        memberSigner,

        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
        clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
        rent: anchor.web3.SYSVAR_RENT_PUBKEY,
      },
      signers: [pendingWithdrawal],
      instructions: [
        await registry.account.pendingWithdrawal.createInstruction(
          pendingWithdrawal
        ),
      ],
    });

    const vaultPw = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vaultPw
    );
    const vaultStake = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vaultStake
    );
    const spt = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.spt
    );

    assert.ok(vaultPw.amount.eq(new anchor.BN(20)));
    assert.ok(vaultStake.amount.eq(new anchor.BN(0)));
    assert.ok(spt.amount.eq(new anchor.BN(0)));
  });

  const tryEndUnstake = async () => {
    await registry.rpc.endUnstake({
      accounts: {
        registrar: registrar.publicKey,

        member: member.publicKey,
        beneficiary: provider.wallet.publicKey,
        pendingWithdrawal: pendingWithdrawal.publicKey,

        vault: balances.vault,
        vaultPw: balances.vaultPw,

        memberSigner,

        clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
      },
    });
  };

  it("Fails to end unstaking before timelock", async () => {
    await assert.rejects(
      async () => {
        await tryEndUnstake();
      },
      (err) => {
        assert.equal(err.code, 109);
        assert.equal(err.msg, "The unstake timelock has not yet expired.");
        return true;
      }
    );
  });

  it("Waits for the unstake period to end", async () => {
    await serumCmn.sleep(5000);
  });

  it("Unstake finalizes (unlocked)", async () => {
    await tryEndUnstake();

    const vault = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vault
    );
    const vaultPw = await serumCmn.getTokenAccount(
      provider,
      memberAccount.balances.vaultPw
    );

    assert.ok(vault.amount.eq(new anchor.BN(120)));
    assert.ok(vaultPw.amount.eq(new anchor.BN(0)));
  });

  it("Withdraws deposits (unlocked)", async () => {
    const token = await serumCmn.createTokenAccount(
      provider,
      mint,
      provider.wallet.publicKey
    );
    const withdrawAmount = new anchor.BN(100);
    await registry.rpc.withdraw(withdrawAmount, {
      accounts: {
        registrar: registrar.publicKey,
        member: member.publicKey,
        beneficiary: provider.wallet.publicKey,
        vault: memberAccount.balances.vault,
        memberSigner,
        depositor: token,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
      },
    });

    const tokenAccount = await serumCmn.getTokenAccount(provider, token);
    assert.ok(tokenAccount.amount.eq(withdrawAmount));
  });

  it("Should succesfully unlock a locked reward after unstaking", async () => {
    const token = await serumCmn.createTokenAccount(
      provider,
      mint,
      provider.wallet.publicKey
    );

    const withdrawAmount = new anchor.BN(7);
    await lockup.rpc.withdraw(withdrawAmount, {
      accounts: {
        vesting: vendoredVesting.publicKey,
        beneficiary: provider.wallet.publicKey,
        token,
        vault: vendoredVestingVault.publicKey,
        vestingSigner: vendoredVestingSigner,
        tokenProgram: TokenInstructions.TOKEN_PROGRAM_ID,
        clock: anchor.web3.SYSVAR_CLOCK_PUBKEY,
      },
      // TODO: trait methods generated on the client. Until then, we need to manually
      //       specify the account metas here.
      remainingAccounts: [
        { pubkey: registry.programId, isWritable: false, isSigner: false },
        { pubkey: member.publicKey, isWritable: false, isSigner: false },
        { pubkey: balances.spt, isWritable: false, isSigner: false },
        { pubkey: balancesLocked.spt, isWritable: false, isSigner: false },
      ],
    });
    const tokenAccount = await serumCmn.getTokenAccount(provider, token);
    assert.ok(tokenAccount.amount.eq(withdrawAmount));
  });
});
