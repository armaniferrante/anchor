# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

**Note:** Version 0 of Semantic Versioning is handled differently from version 1 and above.
The minor version will be incremented upon a breaking change and the patch version will be
incremented for features.

## [Unreleased]

### Features

* cli: Embed workspace programs into local validator genesis when testing.
* cli: Stream program logs to `.anchor/program-logs` directory when testing.
* spl: Add shared memory api.
* lang/attribute/access-control: Allow specifying multiple modifier functions.
* lang/syn: Allow state structs that don't have a ctor or impl block (just trait implementations).

## [0.2.0] - 2021-02-08

### Features

* lang: Adds the ability to create and use CPI program interfaces [(#66)](https://github.com/project-serum/anchor/pull/66/files?file-filters%5B%5D=).

### Breaking Changes

* lang, client, ts: Migrate from rust enum based method dispatch to a variant of sighash [(#64)](https://github.com/project-serum/anchor/pull/64).

## [0.1.0] - 2021-01-31

Initial release.

### Includes

* lang: `anchor-lang` crate providing a Rust eDSL for Solana.
* lang/attribute/access-control: Internal attribute macro for function modifiers.
* lang/attribute/account: Internal attribute macro for defining Anchor accounts.
* lang/attribute/error: Internal attribute macro for defining Anchor program errors.
* lang/attribute/program: Internal attribute macro for defining an Anchor program.
* lang/attribute/state: Internal attribute macro for defining an Anchor program state struct.
* lang/derive/accounts: Internal derive macro for defining deserialized account structs.
* lang/syn: Internal crate for parsing the Anchor eDSL, generating code, and an IDL.
* spl: `anchor-spl` crate providing CPI clients for Anchor programs.
* client: `anchor-client` crate providing Rust clients for Anchor programs.
* ts: `@project-serum/anchor` package for generating TypeScript clients.
* cli: Command line interface for managing Anchor programs.
