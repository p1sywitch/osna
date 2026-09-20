#!/usr/bin/env bash
set -e
cd "$(dirname "$0")"
command -v node >/dev/null || { echo "Node.js 18+ gerekli"; exit 1; }
[ -f .env ] || cp .env.example .env
npm install
echo "Kurulum tamam. .env ayarla ve npm start calistir."
