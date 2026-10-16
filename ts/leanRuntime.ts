/**
 * Lean as an alternative runtime: the same trigger signature, but the result comes
 * from the compiled, verified Lean binary rather than from TypeScript.
 *
 * The boundary is one JSON envelope in and one JSON object out:
 *   stdin  { "data": TemplateModel, "request": Request, "now": ISO-8601 }
 *   stdout { "result": Response } | { "error": string }
 *
 * In the template engine this would sit behind a pluggable logic runtime, e.g.
 * `logic/logic.lean` compiled at archive build time, with this adapter (or a WASM
 * build of the same binary) invoked from `TemplateArchiveProcessor.trigger`.
 */
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import type { TemplateModel, LateDeliveryRequest, LateDeliveryResponse } from './logic.ts';

export const LEAN_BIN =
  process.env.LATEDELIVERY_BIN ??
  join(dirname(fileURLToPath(import.meta.url)), '..', 'lean', '.lake', 'build', 'bin', 'latedelivery');

export function trigger(data: TemplateModel, request: LateDeliveryRequest, now: string): LateDeliveryResponse {
  const run = spawnSync(LEAN_BIN, ['trigger'], { input: JSON.stringify({ data, request, now }), encoding: 'utf8' });
  if (run.error) throw run.error;
  const out = JSON.parse(run.stdout);
  if (out.error) throw new Error(out.error);
  return out.result;
}

// Usage: node --experimental-strip-types ts/leanRuntime.ts examples/envelope.json
if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const { readFileSync } = await import('node:fs');
  const env = JSON.parse(readFileSync(process.argv[2] ?? 0, 'utf8'));
  console.log(JSON.stringify(trigger(env.data, env.request, env.now), null, 2));
}
