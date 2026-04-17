#!/usr/bin/env bash
# Verify extra Dafny files not covered by lsc check.
set -e
cd "$(dirname "$0")"

dafny verify --standard-libraries  --verification-time-limit 1000 src/domain.proofs.dfy
