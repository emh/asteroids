const canvas = document.getElementById("game");
const ctx = canvas.getContext("2d");
const mobileControlsRoot = document.getElementById("mobile-controls");
const mobileDpadZone = document.getElementById("dpad-zone");
const mobileDpadThumb = document.getElementById("dpad-thumb");
const mobileFireButton = document.getElementById("fire-btn");

const ASTEROID_RADII = {
  3: 56,
  2: 34,
  1: 20,
};

const POINTS = {
  3: 20,
  2: 50,
  1: 100,
};

const SHIP_ROTATION_SPEED = 3.6;
const SHIP_THRUST = 340;
const SHIP_REVERSE_THRUST = 255;
const SHIP_DRAG = 0.986;
const SHIP_BASE_MAX_SPEED = 520;
const SHIP_SPEED_BOOST_MAX_SPEED = 720;
const SHIP_SPEED_BOOST_THRUST_MULTIPLIER = 1.45;
const SHIP_SPEED_BOOST_DRAG = 0.992;
const BULLET_SPEED = 520;
const BULLET_LIFETIME = 1.2;
const SHOOT_COOLDOWN = 0.18;
const STARTING_LIVES = 3;
const MOBILE_GAME_RENDER_SCALE = 0.5;
const WORLD_SCALE = 6;
const WORLD_MIN_SIZE = 5400;
const SHIP_EXPLOSION_DURATION = 0.9;
const CAMERA_MAX_OFFSET_FRACTION = 0.25;
const CAMERA_THRUST_ACCEL = 1300;
const CAMERA_CENTER_STIFFNESS = 11;
const CAMERA_CENTER_DAMPING = 7.2;
const CAMERA_MAX_SPEED = 820;
const CAMERA_VELOCITY_DRAG = 0.9;
const ASTEROID_SPAWN_BASE_RATE = 0.018;
const ASTEROID_SPAWN_GROWTH_RATE = 0.0012;
const ASTEROID_SPAWN_MAX_RATE = 0.19;
const ENEMY_SPAWN_BASE_RATE = 0.004;
const ENEMY_SPAWN_GROWTH_RATE = 0.00055;
const ENEMY_SPAWN_MAX_RATE = 0.065;
const BASE_MAX_ASTEROIDS = 12;
const MAX_ASTEROIDS_CAP = 32;
const BASE_MAX_ENEMIES = 1;
const MAX_ENEMIES_CAP = 8;
const ENEMY_RADIUS = 16;
const ENEMY_ACCELERATION = 170;
const ENEMY_MAX_SPEED = 165;
const ENEMY_CHASE_SPEED = 220;
const ENEMY_DRAG = 0.987;
const ENEMY_TURN_RATE = 3.6;
const ENEMY_AVOID_DISTANCE = 160;
const ENEMY_AVOID_FORCE = 3;
const ENEMY_WANDER_FORCE = 1.05;
const ENEMY_CHASE_FORCE = 2.1;
const ENEMY_RADAR_RANGE = 980;
const ENEMY_FIRE_COOLDOWN_MIN = 1.2;
const ENEMY_FIRE_COOLDOWN_MAX = 2.4;
const ENEMY_BULLET_SPEED = 360;
const ENEMY_BULLET_LIFETIME = 4.2;
const ENEMY_POINTS = 180;
const SHIELD_HITS_PER_PICKUP = 3;
const FIRE_RATE_MULTIPLIER = 0.42;
const FIRE_RATE_DURATION = 13;
const SPEED_BOOST_DURATION = 11;
const POWERUP_RADIUS = 14;
const POWERUP_SPAWN_BASE_RATE = 0.0085;
const POWERUP_SPAWN_GROWTH_RATE = 0.00032;
const POWERUP_SPAWN_MAX_RATE = 0.048;
const MAX_POWERUPS = 4;
const RADAR_PADDING = 24;
const RADAR_SIZE = 168;
const RADAR_RANGE = 1500;
const DEBRIS_COUNTS = {
  3: 24,
  2: 16,
  1: 10,
};

const STAR_LAYER_CONFIGS = [
  { density: 1 / 24000, depth: 0.14, sizeMin: 0.8, sizeMax: 1.4, drift: 3.5 },
  { density: 1 / 16000, depth: 0.34, sizeMin: 1.0, sizeMax: 2.1, drift: 6.2 },
  { density: 1 / 10000, depth: 0.62, sizeMin: 1.3, sizeMax: 2.8, drift: 9.4 },
];

const keys = new Set();
const mobileInput = {
  enabled: false,
  firePointerIds: new Set(),
  padPointerId: null,
  padVectorX: 0,
  padVectorY: 0,
  padActions: {
    up: false,
    down: false,
    left: false,
    right: false,
  },
};
let starLayers = [];
let galaxies = [];
let ambientTime = 0;
const world = {
  width: 0,
  height: 0,
};
const camera = {
  offsetX: 0,
  offsetY: 0,
  velocityX: 0,
  velocityY: 0,
};

let screen = "welcome";
let gameOver = false;
let score = 0;
let lives = STARTING_LIVES;
let ship;
let bullets = [];
let asteroids = [];
let enemies = [];
let enemyBullets = [];
let powerUps = [];
let debris = [];
let shootTimer = 0;
let lastTimestamp = 0;
let shipDestroyed = false;
let pendingRespawn = false;
let pendingGameOver = false;
let shipExplosionTimer = 0;
let gameTime = 0;
let asteroidSpawnAccumulator = 0;
let enemySpawnAccumulator = 0;
let powerUpSpawnAccumulator = 0;
let shieldCharges = 0;
let fireRateBoostTimer = 0;
let speedBoostTimer = 0;
let lastTouchEndTime = 0;
let gameRenderScale = 1;

function wrapValue(value, max) {
  if (max <= 0) {
    return value;
  }

  const wrapped = value % max;
  return wrapped < 0 ? wrapped + max : wrapped;
}

function torusDelta(from, to, max) {
  let delta = to - from;
  if (delta > max * 0.5) {
    delta -= max;
  } else if (delta < -max * 0.5) {
    delta += max;
  }
  return delta;
}

function relativeToShip(x, y) {
  return {
    x: torusDelta(ship.x, x, world.width),
    y: torusDelta(ship.y, y, world.height),
  };
}

function worldToScreen(x, y) {
  const relative = relativeToShip(x, y);
  return {
    x: canvas.width * 0.5 + camera.offsetX + relative.x,
    y: canvas.height * 0.5 + camera.offsetY + relative.y,
  };
}

function shouldRenderAt(x, y, padding = 0) {
  return (
    x >= -padding &&
    x <= canvas.width + padding &&
    y >= -padding &&
    y <= canvas.height + padding
  );
}

function hasTouchAction(action) {
  if (action === "fire") {
    return mobileInput.firePointerIds.size > 0;
  }
  return Boolean(mobileInput.padActions[action]);
}

function setPadActionsFromVector(x, y) {
  const deadZone = 0.18;
  const axisThreshold = 0.28;
  const magnitude = Math.hypot(x, y);

  if (magnitude < deadZone) {
    mobileInput.padActions.up = false;
    mobileInput.padActions.down = false;
    mobileInput.padActions.left = false;
    mobileInput.padActions.right = false;
    return;
  }

  mobileInput.padActions.up = y < -axisThreshold;
  mobileInput.padActions.down = y > axisThreshold;
  mobileInput.padActions.left = x < -axisThreshold;
  mobileInput.padActions.right = x > axisThreshold;
}

function updateDpadThumb() {
  if (!mobileDpadZone || !mobileDpadThumb) {
    return;
  }

  const maxTravel = mobileDpadZone.clientWidth * 0.24;
  const offsetX = mobileInput.padVectorX * maxTravel;
  const offsetY = mobileInput.padVectorY * maxTravel;
  mobileDpadThumb.style.transform = `translate(calc(-50% + ${offsetX}px), calc(-50% + ${offsetY}px))`;
}

function resetPadInput() {
  mobileInput.padPointerId = null;
  mobileInput.padVectorX = 0;
  mobileInput.padVectorY = 0;
  mobileInput.padActions.up = false;
  mobileInput.padActions.down = false;
  mobileInput.padActions.left = false;
  mobileInput.padActions.right = false;

  if (mobileDpadZone) {
    mobileDpadZone.classList.remove("is-active");
  }

  updateDpadThumb();
}

function updatePadFromPointer(clientX, clientY) {
  if (!mobileDpadZone) {
    return;
  }

  const rect = mobileDpadZone.getBoundingClientRect();
  const radius = Math.min(rect.width, rect.height) * 0.5;
  if (radius <= 0) {
    resetPadInput();
    return;
  }

  const centerX = rect.left + rect.width * 0.5;
  const centerY = rect.top + rect.height * 0.5;
  let normalizedX = (clientX - centerX) / radius;
  let normalizedY = (clientY - centerY) / radius;
  const magnitude = Math.hypot(normalizedX, normalizedY);

  if (magnitude > 1) {
    normalizedX /= magnitude;
    normalizedY /= magnitude;
  }

  mobileInput.padVectorX = normalizedX;
  mobileInput.padVectorY = normalizedY;
  setPadActionsFromVector(normalizedX, normalizedY);
  mobileDpadZone.classList.add("is-active");
  updateDpadThumb();
}

function updateFireButtonVisual() {
  if (!mobileFireButton) {
    return;
  }
  mobileFireButton.classList.toggle("is-active", mobileInput.firePointerIds.size > 0);
}

function releaseTouchPointer(pointerId) {
  if (mobileInput.padPointerId === pointerId) {
    resetPadInput();
  }

  if (mobileInput.firePointerIds.delete(pointerId)) {
    updateFireButtonVisual();
  }
}

function clearTouchActions() {
  mobileInput.firePointerIds.clear();
  updateFireButtonVisual();
  resetPadInput();
}

function shouldUseMobileControls() {
  const hasTouch = navigator.maxTouchPoints > 0 || "ontouchstart" in window;
  if (!hasTouch) {
    return false;
  }

  return window.matchMedia("(max-width: 1024px), (max-height: 900px)").matches;
}

function refreshMobileControlsLayout() {
  const enabled = shouldUseMobileControls();
  mobileInput.enabled = enabled;
  document.body.classList.toggle("mobile-controls-enabled", enabled);

  if (mobileControlsRoot) {
    mobileControlsRoot.hidden = !enabled;
  }

  clearTouchActions();
}

function setupMobileControls() {
  if (!mobileControlsRoot) {
    return;
  }

  if (mobileDpadZone) {
    mobileDpadZone.addEventListener("pointerdown", (event) => {
      if (!mobileInput.enabled) {
        return;
      }

      if (event.pointerType === "mouse" && event.button !== 0) {
        return;
      }

      if (mobileInput.padPointerId !== null && mobileInput.padPointerId !== event.pointerId) {
        return;
      }

      event.preventDefault();
      mobileInput.padPointerId = event.pointerId;
      if (mobileDpadZone.setPointerCapture) {
        mobileDpadZone.setPointerCapture(event.pointerId);
      }
      updatePadFromPointer(event.clientX, event.clientY);
    });

    mobileDpadZone.addEventListener("pointermove", (event) => {
      if (!mobileInput.enabled || mobileInput.padPointerId !== event.pointerId) {
        return;
      }

      event.preventDefault();
      updatePadFromPointer(event.clientX, event.clientY);
    });

    mobileDpadZone.addEventListener("pointerup", (event) => {
      releaseTouchPointer(event.pointerId);
    });
    mobileDpadZone.addEventListener("pointercancel", (event) => {
      releaseTouchPointer(event.pointerId);
    });
  }

  if (mobileFireButton) {
    mobileFireButton.addEventListener("pointerdown", (event) => {
      if (!mobileInput.enabled) {
        return;
      }

      if (event.pointerType === "mouse" && event.button !== 0) {
        return;
      }

      event.preventDefault();
      mobileInput.firePointerIds.add(event.pointerId);
      updateFireButtonVisual();
      if (mobileFireButton.setPointerCapture) {
        mobileFireButton.setPointerCapture(event.pointerId);
      }

      if (screen === "playing") {
        fireBullet();
      } else if (screen === "welcome") {
        startGame();
      }
    });

    mobileFireButton.addEventListener("pointerup", (event) => {
      releaseTouchPointer(event.pointerId);
    });
    mobileFireButton.addEventListener("pointercancel", (event) => {
      releaseTouchPointer(event.pointerId);
    });
  }

  mobileControlsRoot.addEventListener("contextmenu", (event) => {
    event.preventDefault();
  });

  window.addEventListener("pointerup", (event) => {
    releaseTouchPointer(event.pointerId);
  });
  window.addEventListener("pointercancel", (event) => {
    releaseTouchPointer(event.pointerId);
  });
}

function isThrusting() {
  return keys.has("ArrowUp") || keys.has("KeyW") || hasTouchAction("up");
}

function isReverseThrusting() {
  return keys.has("ArrowDown") || keys.has("KeyS") || hasTouchAction("down");
}

function getMobileTurnInput() {
  if (!mobileInput.enabled || mobileInput.padPointerId === null) {
    return 0;
  }

  const x = mobileInput.padVectorX;
  const absX = Math.abs(x);
  if (absX < 0.03) {
    return 0;
  }

  const curvedTurn = absX * absX;
  return x < 0 ? -curvedTurn : curvedTurn;
}

function getTurnInput() {
  let turnInput = 0;
  if (keys.has("ArrowLeft") || keys.has("KeyA")) {
    turnInput -= 1;
  }
  if (keys.has("ArrowRight") || keys.has("KeyD")) {
    turnInput += 1;
  }

  turnInput += getMobileTurnInput();
  return clamp(turnInput, -1, 1);
}

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function shortestAngleDelta(from, to) {
  let delta = to - from;
  while (delta > Math.PI) {
    delta -= Math.PI * 2;
  }
  while (delta < -Math.PI) {
    delta += Math.PI * 2;
  }
  return delta;
}

function torusDistance(x1, y1, x2, y2) {
  const dx = torusDelta(x1, x2, world.width);
  const dy = torusDelta(y1, y2, world.height);
  return Math.hypot(dx, dy);
}

function randomSpawnAroundShip(minDistance, maxDistance) {
  const angle = Math.random() * Math.PI * 2;
  const distance = minDistance + Math.random() * (maxDistance - minDistance);
  return {
    x: wrapValue(ship.x + Math.cos(angle) * distance, world.width),
    y: wrapValue(ship.y + Math.sin(angle) * distance, world.height),
  };
}

function ensureWorldSize() {
  if (world.width > 0 && world.height > 0) {
    return;
  }

  world.width = Math.max(
    WORLD_MIN_SIZE,
    Math.round(window.innerWidth * WORLD_SCALE),
  );
  world.height = Math.max(
    WORLD_MIN_SIZE,
    Math.round(window.innerHeight * WORLD_SCALE),
  );
}

function resizeCanvas() {
  refreshMobileControlsLayout();
  gameRenderScale = mobileInput.enabled ? MOBILE_GAME_RENDER_SCALE : 1;

  const displayWidth = Math.max(1, Math.floor(canvas.clientWidth || window.innerWidth));
  const displayHeight = Math.max(1, Math.floor(canvas.clientHeight || window.innerHeight));
  canvas.width = Math.max(1, Math.floor(displayWidth / gameRenderScale));
  canvas.height = Math.max(1, Math.floor(displayHeight / gameRenderScale));
  ensureWorldSize();
  buildStarField();

  if (!ship) {
    resetShip();
  }
}

function buildStarField() {
  const area = canvas.width * canvas.height;

  starLayers = STAR_LAYER_CONFIGS.map((config, layerIndex) => {
    const count = Math.max(24, Math.floor(area * config.density));

    return {
      ...config,
      offsetX: Math.random() * canvas.width,
      offsetY: Math.random() * canvas.height,
      stars: Array.from({ length: count }, () => {
        let tint = "238,244,255";
        if (layerIndex === 0 && Math.random() > 0.35) {
          tint = "190,214,255";
        } else if (layerIndex === 2 && Math.random() > 0.6) {
          tint = "255,236,210";
        }

        return {
          x: Math.random() * canvas.width,
          y: Math.random() * canvas.height,
          size:
            config.sizeMin +
            Math.random() * (config.sizeMax - config.sizeMin),
          alpha: 0.22 + Math.random() * 0.7,
          twinkle: 0.65 + Math.random() * 1.75,
          phase: Math.random() * Math.PI * 2,
          tint,
        };
      }),
    };
  });

  const hues = [24, 38, 166, 196, 208];
  const galaxyCount = Math.max(
    3,
    Math.floor(Math.min(canvas.width, canvas.height) / 420),
  );

  galaxies = Array.from({ length: galaxyCount }, () => ({
    x: Math.random() * canvas.width,
    y: Math.random() * canvas.height,
    radius: 140 + Math.random() * 280,
    hue: hues[Math.floor(Math.random() * hues.length)] + (Math.random() * 12 - 6),
    alpha: 0.09 + Math.random() * 0.11,
    driftX: (Math.random() * 2 - 1) * (2 + Math.random() * 4),
    driftY: (Math.random() * 2 - 1) * (2 + Math.random() * 4),
    pulse: Math.random() * Math.PI * 2,
    pulseRate: 0.15 + Math.random() * 0.24,
  }));
}

function resetShip() {
  ship = {
    x: world.width / 2,
    y: world.height / 2,
    vx: 0,
    vy: 0,
    angle: -Math.PI / 2,
    radius: 18,
    invulnerable: 0,
  };
}

function randomAsteroidSpawn() {
  const minDistance = Math.max(240, Math.min(canvas.width, canvas.height) * 0.42);
  const maxDistance = Math.max(canvas.width, canvas.height) * 1.05;
  return randomSpawnAroundShip(minDistance, maxDistance);
}

function createAsteroid(x, y, size, vx, vy) {
  const angle = Math.random() * Math.PI * 2;
  const difficultyScale = 1 + Math.min(2.4, gameTime / 140) * 0.45;
  const speed = (26 + Math.random() * 38) * difficultyScale;
  const velocityX = vx ?? Math.cos(angle) * speed;
  const velocityY = vy ?? Math.sin(angle) * speed;
  const radius = ASTEROID_RADII[size];
  const ridgeCount = 2 + Math.floor(Math.random() * 3);
  const facetCount = 3 + Math.floor(Math.random() * 3);

  return {
    x,
    y,
    vx: velocityX,
    vy: velocityY,
    size,
    radius,
    rotation: Math.random() * Math.PI * 2,
    spin: (Math.random() * 2 - 1) * 0.55,
    offsets: Array.from({ length: 10 }, () => 0.75 + Math.random() * 0.5),
    ridges: Array.from({ length: ridgeCount }, () => {
      const startAngle = Math.random() * Math.PI * 2;
      const direction = Math.random() > 0.5 ? 1 : -1;
      return {
        startAngle,
        endAngle:
          startAngle + direction * (0.55 + Math.random() * 0.8),
        startScale: 0.2 + Math.random() * 0.24,
        endScale: 0.52 + Math.random() * 0.28,
        alpha: 0.12 + Math.random() * 0.15,
        width: 1 + Math.random() * 1.2,
      };
    }),
    facets: Array.from({ length: facetCount }, (_, index) => ({
      angle: Math.random() * Math.PI * 2,
      arc: 0.32 + Math.random() * 0.35,
      edgeA: 0.62 + Math.random() * 0.24,
      edgeB: 0.62 + Math.random() * 0.24,
      inner: 0.16 + Math.random() * 0.2,
      alpha: 0.07 + Math.random() * 0.09,
      tone: index % 2 === 0 ? "238, 233, 220" : "42, 44, 50",
    })),
  };
}

function createEnemy(x, y) {
  const heading = Math.random() * Math.PI * 2;
  const baseSpeed = 35 + Math.random() * 70;

  return {
    x,
    y,
    vx: Math.cos(heading) * baseSpeed,
    vy: Math.sin(heading) * baseSpeed,
    angle: heading,
    radius: ENEMY_RADIUS,
    wanderAngle: heading + (Math.random() * 2 - 1) * 1.2,
    shootCooldown:
      ENEMY_FIRE_COOLDOWN_MIN +
      Math.random() * (ENEMY_FIRE_COOLDOWN_MAX - ENEMY_FIRE_COOLDOWN_MIN),
    radarRange: ENEMY_RADAR_RANGE * (0.84 + Math.random() * 0.36),
    aggression: 0.68 + Math.random() * 0.62,
    alert: false,
  };
}

function randomEnemySpawn() {
  const minDistance = Math.max(340, Math.min(canvas.width, canvas.height) * 0.65);
  const maxDistance = Math.max(canvas.width, canvas.height) * 1.3;
  return randomSpawnAroundShip(minDistance, maxDistance);
}

function spawnRandomAsteroid() {
  for (let i = 0; i < 26; i += 1) {
    const spawn = randomAsteroidSpawn();
    if (torusDistance(spawn.x, spawn.y, ship.x, ship.y) < 280) {
      continue;
    }

    let tooClose = false;
    for (const asteroid of asteroids) {
      if (torusDistance(spawn.x, spawn.y, asteroid.x, asteroid.y) < asteroid.radius + 140) {
        tooClose = true;
        break;
      }
    }

    if (tooClose) {
      continue;
    }

    asteroids.push(createAsteroid(spawn.x, spawn.y, 3));
    return true;
  }

  return false;
}

function spawnRandomEnemy() {
  for (let i = 0; i < 30; i += 1) {
    const spawn = randomEnemySpawn();
    if (torusDistance(spawn.x, spawn.y, ship.x, ship.y) < 360) {
      continue;
    }

    let blocked = false;
    for (const asteroid of asteroids) {
      if (
        torusDistance(spawn.x, spawn.y, asteroid.x, asteroid.y) <
        asteroid.radius + 220
      ) {
        blocked = true;
        break;
      }
    }

    if (blocked) {
      continue;
    }

    for (const enemy of enemies) {
      if (torusDistance(spawn.x, spawn.y, enemy.x, enemy.y) < enemy.radius + 180) {
        blocked = true;
        break;
      }
    }

    if (blocked) {
      continue;
    }

    enemies.push(createEnemy(spawn.x, spawn.y));
    return true;
  }

  return false;
}

function createPowerUp(x, y, type) {
  return {
    x,
    y,
    type,
    radius: POWERUP_RADIUS,
    rotation: Math.random() * Math.PI * 2,
    spin: (Math.random() * 2 - 1) * 0.75,
    pulse: Math.random() * Math.PI * 2,
    pulseRate: 1.6 + Math.random() * 1.4,
  };
}

function randomPowerUpSpawn() {
  const minDistance = Math.max(260, Math.min(canvas.width, canvas.height) * 0.48);
  const maxDistance = Math.max(canvas.width, canvas.height) * 1.18;
  return randomSpawnAroundShip(minDistance, maxDistance);
}

function spawnRandomPowerUp() {
  for (let i = 0; i < 30; i += 1) {
    const spawn = randomPowerUpSpawn();
    if (torusDistance(spawn.x, spawn.y, ship.x, ship.y) < 240) {
      continue;
    }

    let blocked = false;
    for (const asteroid of asteroids) {
      if (
        torusDistance(spawn.x, spawn.y, asteroid.x, asteroid.y) <
        asteroid.radius + 110
      ) {
        blocked = true;
        break;
      }
    }

    if (blocked) {
      continue;
    }

    for (const enemy of enemies) {
      if (torusDistance(spawn.x, spawn.y, enemy.x, enemy.y) < enemy.radius + 95) {
        blocked = true;
        break;
      }
    }

    if (blocked) {
      continue;
    }

    for (const powerUp of powerUps) {
      if (torusDistance(spawn.x, spawn.y, powerUp.x, powerUp.y) < powerUp.radius + 80) {
        blocked = true;
        break;
      }
    }

    if (blocked) {
      continue;
    }

    const roll = Math.random();
    const type =
      roll < 0.36
        ? "shield"
        : roll < 0.66
          ? "fire_rate"
          : roll < 0.95
            ? "speed"
            : "life";
    powerUps.push(createPowerUp(spawn.x, spawn.y, type));
    return true;
  }

  return false;
}

function spawnInitialAsteroids(count) {
  for (let i = 0; i < count; i += 1) {
    spawnRandomAsteroid();
  }
}

function startGame() {
  screen = "playing";
  gameOver = false;
  score = 0;
  lives = STARTING_LIVES;
  shootTimer = 0;
  gameTime = 0;
  asteroidSpawnAccumulator = 0;
  enemySpawnAccumulator = 0;
  powerUpSpawnAccumulator = 0;
  bullets = [];
  enemyBullets = [];
  asteroids = [];
  enemies = [];
  powerUps = [];
  debris = [];
  shieldCharges = 0;
  fireRateBoostTimer = 0;
  speedBoostTimer = 0;
  shipDestroyed = false;
  pendingRespawn = false;
  pendingGameOver = false;
  shipExplosionTimer = 0;
  camera.offsetX = 0;
  camera.offsetY = 0;
  camera.velocityX = 0;
  camera.velocityY = 0;
  resetShip();
  spawnInitialAsteroids(5);
}

function endGame() {
  screen = "welcome";
  gameOver = true;
}

function wrapPosition(entity) {
  entity.x = wrapValue(entity.x, world.width);
  entity.y = wrapValue(entity.y, world.height);
}

function fireBullet() {
  if (shootTimer > 0 || shipDestroyed) {
    return;
  }

  const noseDistance = ship.radius + 2;
  bullets.push({
    x: ship.x + Math.cos(ship.angle) * noseDistance,
    y: ship.y + Math.sin(ship.angle) * noseDistance,
    vx: ship.vx + Math.cos(ship.angle) * BULLET_SPEED,
    vy: ship.vy + Math.sin(ship.angle) * BULLET_SPEED,
    radius: 2.5,
    life: BULLET_LIFETIME,
  });

  const cooldownMultiplier = fireRateBoostTimer > 0 ? FIRE_RATE_MULTIPLIER : 1;
  shootTimer = SHOOT_COOLDOWN * cooldownMultiplier;
}

function spawnDebrisField(asteroid) {
  const count = DEBRIS_COUNTS[asteroid.size];
  const baseSpeed = Math.hypot(asteroid.vx, asteroid.vy);

  for (let i = 0; i < count; i += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed =
      60 +
      Math.random() * 140 +
      asteroid.size * 16 +
      baseSpeed * (0.25 + Math.random() * 0.35);
    const tangent = (Math.random() * 2 - 1) * 36;
    const life = 0.32 + Math.random() * 0.34 + asteroid.size * 0.06;
    const length = 2 + asteroid.size * 1.5 + Math.random() * 3.2;
    const width = 0.9 + Math.random() * 1.6;

    debris.push({
      type: "shard",
      x: asteroid.x,
      y: asteroid.y,
      vx:
        asteroid.vx * 0.34 +
        Math.cos(angle) * speed -
        Math.sin(angle) * tangent,
      vy:
        asteroid.vy * 0.34 +
        Math.sin(angle) * speed +
        Math.cos(angle) * tangent,
      rotation: Math.random() * Math.PI * 2,
      spin: (Math.random() * 2 - 1) * 9,
      length,
      width,
      life,
      maxLife: life,
      tint:
        Math.random() > 0.84
          ? "255, 178, 112"
          : Math.random() > 0.5
            ? "202, 197, 188"
            : "163, 160, 156",
    });
  }

  const dustCount = Math.max(5, Math.floor(count * 0.45));
  for (let i = 0; i < dustCount; i += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 28 + Math.random() * 92 + asteroid.size * 10;
    const life = 0.26 + Math.random() * 0.34 + asteroid.size * 0.04;
    const radius = 1.2 + Math.random() * (1.3 + asteroid.size);

    debris.push({
      type: "dust",
      x: asteroid.x,
      y: asteroid.y,
      vx: asteroid.vx * 0.3 + Math.cos(angle) * speed,
      vy: asteroid.vy * 0.3 + Math.sin(angle) * speed,
      radius,
      growth: 0.35 + Math.random() * 0.8,
      life,
      maxLife: life,
      tint: Math.random() > 0.25 ? "145, 153, 168" : "232, 185, 131",
    });
  }
}

function spawnShipExplosion() {
  const baseVx = ship.vx;
  const baseVy = ship.vy;

  debris.push({
    type: "ring",
    x: ship.x,
    y: ship.y,
    vx: baseVx * 0.2,
    vy: baseVy * 0.2,
    radius: ship.radius * 0.3,
    growth: 210,
    lineWidth: 2.2,
    life: SHIP_EXPLOSION_DURATION * 0.72,
    maxLife: SHIP_EXPLOSION_DURATION * 0.72,
    tint: "255, 188, 112",
  });

  for (let i = 0; i < 34; i += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 90 + Math.random() * 220;
    const life = 0.35 + Math.random() * 0.45;
    const length = 3 + Math.random() * 6.5;

    debris.push({
      type: "shard",
      x: ship.x,
      y: ship.y,
      vx: baseVx * 0.4 + Math.cos(angle) * speed,
      vy: baseVy * 0.4 + Math.sin(angle) * speed,
      rotation: Math.random() * Math.PI * 2,
      spin: (Math.random() * 2 - 1) * 11,
      length,
      width: 1 + Math.random() * 1.8,
      life,
      maxLife: life,
      tint:
        Math.random() > 0.72
          ? "255, 225, 168"
          : Math.random() > 0.44
            ? "255, 152, 86"
            : "178, 221, 255",
      glow: true,
    });
  }

  for (let i = 0; i < 22; i += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 34 + Math.random() * 122;
    const life = 0.45 + Math.random() * 0.45;
    const radius = 1.6 + Math.random() * 3.8;

    debris.push({
      type: "dust",
      x: ship.x,
      y: ship.y,
      vx: baseVx * 0.3 + Math.cos(angle) * speed,
      vy: baseVy * 0.3 + Math.sin(angle) * speed,
      radius,
      growth: 0.7 + Math.random() * 1.5,
      life,
      maxLife: life,
      tint:
        Math.random() > 0.6
          ? "255, 170, 108"
          : Math.random() > 0.3
            ? "172, 188, 214"
            : "242, 214, 176",
    });
  }
}

function destroyShip() {
  spawnShipExplosion();
  shipDestroyed = true;
  shipExplosionTimer = SHIP_EXPLOSION_DURATION;
  ship.vx = 0;
  ship.vy = 0;
  shootTimer = 0;
}

function registerShipHit() {
  if (shieldCharges > 0) {
    shieldCharges -= 1;
    ship.invulnerable = Math.max(ship.invulnerable, 0.6);

    debris.push({
      type: "ring",
      x: ship.x,
      y: ship.y,
      vx: ship.vx * 0.12,
      vy: ship.vy * 0.12,
      radius: ship.radius * 0.55,
      growth: 185,
      lineWidth: 2.3,
      life: 0.42,
      maxLife: 0.42,
      tint: "142, 238, 255",
    });
    return;
  }

  lives -= 1;
  destroyShip();
  pendingGameOver = lives <= 0;
  pendingRespawn = lives > 0;
}

function spawnEnemyDebris(enemy) {
  for (let i = 0; i < 18; i += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 55 + Math.random() * 150;
    const life = 0.26 + Math.random() * 0.36;
    const length = 2.5 + Math.random() * 3.8;

    debris.push({
      type: "shard",
      x: enemy.x,
      y: enemy.y,
      vx: enemy.vx * 0.35 + Math.cos(angle) * speed,
      vy: enemy.vy * 0.35 + Math.sin(angle) * speed,
      rotation: Math.random() * Math.PI * 2,
      spin: (Math.random() * 2 - 1) * 10,
      length,
      width: 1 + Math.random() * 1.8,
      life,
      maxLife: life,
      tint:
        Math.random() > 0.62
          ? "255, 150, 99"
          : Math.random() > 0.38
            ? "255, 214, 170"
            : "150, 209, 255",
      glow: true,
    });
  }

  for (let i = 0; i < 10; i += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 30 + Math.random() * 90;
    const life = 0.28 + Math.random() * 0.34;
    debris.push({
      type: "dust",
      x: enemy.x,
      y: enemy.y,
      vx: enemy.vx * 0.2 + Math.cos(angle) * speed,
      vy: enemy.vy * 0.2 + Math.sin(angle) * speed,
      radius: 1.6 + Math.random() * 3.2,
      growth: 0.4 + Math.random() * 0.8,
      life,
      maxLife: life,
      tint: Math.random() > 0.5 ? "255, 187, 128" : "146, 170, 204",
    });
  }
}

function fireEnemyBullet(enemy, toShipX, toShipY, distanceToShip) {
  const leadTime = Math.min(1.1, distanceToShip / ENEMY_BULLET_SPEED);
  const aimX = toShipX + ship.vx * leadTime * 0.7;
  const aimY = toShipY + ship.vy * leadTime * 0.7;
  const length = Math.hypot(aimX, aimY);
  if (length < 1) {
    return;
  }

  const dirX = aimX / length;
  const dirY = aimY / length;
  const nose = enemy.radius + 2;
  enemyBullets.push({
    x: wrapValue(enemy.x + dirX * nose, world.width),
    y: wrapValue(enemy.y + dirY * nose, world.height),
    vx: enemy.vx * 0.22 + dirX * ENEMY_BULLET_SPEED,
    vy: enemy.vy * 0.22 + dirY * ENEMY_BULLET_SPEED,
    radius: 2.8,
    life: ENEMY_BULLET_LIFETIME,
  });
}

function hitEnemy(index) {
  const enemy = enemies[index];
  score += ENEMY_POINTS;
  spawnEnemyDebris(enemy);
  enemies.splice(index, 1);
}

function hitAsteroid(index) {
  const asteroid = asteroids[index];
  score += POINTS[asteroid.size];
  spawnDebrisField(asteroid);
  asteroids.splice(index, 1);

  if (asteroid.size > 1) {
    const nextSize = asteroid.size - 1;
    const baseHeading = Math.atan2(asteroid.vy, asteroid.vx);
    const baseSpeed = Math.hypot(asteroid.vy, asteroid.vx) * 1.3;

    for (const spread of [-0.75, 0.75]) {
      const heading = baseHeading + spread + (Math.random() - 0.5) * 0.25;
      const vx = Math.cos(heading) * baseSpeed;
      const vy = Math.sin(heading) * baseSpeed;
      asteroids.push(createAsteroid(asteroid.x, asteroid.y, nextSize, vx, vy));
    }
  }
}

function checkCollisions() {
  for (let i = bullets.length - 1; i >= 0; i -= 1) {
    const bullet = bullets[i];
    let consumed = false;

    for (let j = asteroids.length - 1; j >= 0; j -= 1) {
      const asteroid = asteroids[j];
      const dx = torusDelta(asteroid.x, bullet.x, world.width);
      const dy = torusDelta(asteroid.y, bullet.y, world.height);
      const hitDistance = bullet.radius + asteroid.radius;

      if (dx * dx + dy * dy <= hitDistance * hitDistance) {
        bullets.splice(i, 1);
        hitAsteroid(j);
        consumed = true;
        break;
      }
    }

    if (consumed) {
      continue;
    }

    for (let j = enemies.length - 1; j >= 0; j -= 1) {
      const enemy = enemies[j];
      const dx = torusDelta(enemy.x, bullet.x, world.width);
      const dy = torusDelta(enemy.y, bullet.y, world.height);
      const hitDistance = bullet.radius + enemy.radius * 0.88;

      if (dx * dx + dy * dy <= hitDistance * hitDistance) {
        bullets.splice(i, 1);
        hitEnemy(j);
        break;
      }
    }
  }

  if (!shipDestroyed && ship.invulnerable <= 0) {
    for (let i = enemyBullets.length - 1; i >= 0; i -= 1) {
      const projectile = enemyBullets[i];
      const dx = torusDelta(projectile.x, ship.x, world.width);
      const dy = torusDelta(projectile.y, ship.y, world.height);
      const hitDistance = projectile.radius + ship.radius * 0.7;

      if (dx * dx + dy * dy <= hitDistance * hitDistance) {
        enemyBullets.splice(i, 1);
        registerShipHit();
        return;
      }
    }
  }

  if (shipDestroyed || ship.invulnerable > 0) {
    return;
  }

  for (const asteroid of asteroids) {
    const dx = torusDelta(asteroid.x, ship.x, world.width);
    const dy = torusDelta(asteroid.y, ship.y, world.height);
    const hitDistance = ship.radius * 0.8 + asteroid.radius * 0.9;

    if (dx * dx + dy * dy <= hitDistance * hitDistance) {
      registerShipHit();
      return;
    }
  }

  for (const enemy of enemies) {
    const dx = torusDelta(enemy.x, ship.x, world.width);
    const dy = torusDelta(enemy.y, ship.y, world.height);
    const hitDistance = ship.radius * 0.78 + enemy.radius * 0.78;

    if (dx * dx + dy * dy <= hitDistance * hitDistance) {
      registerShipHit();
      return;
    }
  }
}

function updateBackground(dt) {
  ambientTime += dt;
  const inPlay = screen === "playing" && ship;
  const shipSpeed = inPlay ? Math.hypot(ship.vx, ship.vy) : 0;
  const speedFactor = Math.min(1.8, shipSpeed / 220);

  const parallaxX =
    inPlay
      ? -ship.vx * (0.28 + speedFactor * 0.12)
      : Math.cos(ambientTime * 0.22) * 34;
  const parallaxY =
    inPlay
      ? -ship.vy * (0.28 + speedFactor * 0.12)
      : Math.sin(ambientTime * 0.18) * 24;

  for (const layer of starLayers) {
    const starDepth = 0.55 + layer.depth * 1.15;
    const baseDrift = layer.drift * (1.35 + speedFactor * 0.5);
    const vx = baseDrift + parallaxX * starDepth;
    const vy = baseDrift * 0.18 + parallaxY * starDepth;

    layer.offsetX = wrapValue(layer.offsetX + vx * dt, canvas.width);
    layer.offsetY = wrapValue(layer.offsetY + vy * dt, canvas.height);
  }

  for (const galaxy of galaxies) {
    const nebulaParallax = 0.05 + speedFactor * 0.02;
    galaxy.x = wrapValue(
      galaxy.x + (galaxy.driftX * 0.42 + parallaxX * nebulaParallax) * dt,
      canvas.width,
    );
    galaxy.y = wrapValue(
      galaxy.y + (galaxy.driftY * 0.42 + parallaxY * nebulaParallax) * dt,
      canvas.height,
    );
    galaxy.pulse += galaxy.pulseRate * dt;
  }
}

function updateCamera(dt, thrustInput) {
  let accelX = 0;
  let accelY = 0;

  if (screen === "playing" && !shipDestroyed && thrustInput !== 0) {
    accelX += Math.cos(ship.angle) * CAMERA_THRUST_ACCEL * thrustInput;
    accelY += Math.sin(ship.angle) * CAMERA_THRUST_ACCEL * thrustInput;
  }

  accelX += -camera.offsetX * CAMERA_CENTER_STIFFNESS;
  accelY += -camera.offsetY * CAMERA_CENTER_STIFFNESS;
  accelX += -camera.velocityX * CAMERA_CENTER_DAMPING;
  accelY += -camera.velocityY * CAMERA_CENTER_DAMPING;

  camera.velocityX += accelX * dt;
  camera.velocityY += accelY * dt;

  const speed = Math.hypot(camera.velocityX, camera.velocityY);
  if (speed > CAMERA_MAX_SPEED) {
    const scale = CAMERA_MAX_SPEED / speed;
    camera.velocityX *= scale;
    camera.velocityY *= scale;
  }

  camera.offsetX += camera.velocityX * dt;
  camera.offsetY += camera.velocityY * dt;

  const maxOffset = Math.min(canvas.width, canvas.height) * CAMERA_MAX_OFFSET_FRACTION;
  const offsetMagnitude = Math.hypot(camera.offsetX, camera.offsetY);
  if (offsetMagnitude > maxOffset) {
    const scale = maxOffset / offsetMagnitude;
    camera.offsetX *= scale;
    camera.offsetY *= scale;

    const nx = camera.offsetX / maxOffset;
    const ny = camera.offsetY / maxOffset;
    const outwardVelocity = camera.velocityX * nx + camera.velocityY * ny;
    if (outwardVelocity > 0) {
      camera.velocityX -= nx * outwardVelocity;
      camera.velocityY -= ny * outwardVelocity;
    }
  }

  const drag = Math.pow(CAMERA_VELOCITY_DRAG, dt * 60);
  camera.velocityX *= drag;
  camera.velocityY *= drag;
}

function updateShip(dt, thrustInput) {
  const speedBoostActive = speedBoostTimer > 0;
  const thrustPower = speedBoostActive
    ? SHIP_THRUST * SHIP_SPEED_BOOST_THRUST_MULTIPLIER
    : SHIP_THRUST;
  const reverseThrustPower = speedBoostActive
    ? SHIP_REVERSE_THRUST * SHIP_SPEED_BOOST_THRUST_MULTIPLIER
    : SHIP_REVERSE_THRUST;
  const dragValue = speedBoostActive ? SHIP_SPEED_BOOST_DRAG : SHIP_DRAG;
  const turnInput = getTurnInput();
  if (turnInput !== 0) {
    ship.angle += SHIP_ROTATION_SPEED * turnInput * dt;
  }

  if (thrustInput > 0) {
    ship.vx += Math.cos(ship.angle) * thrustPower * dt;
    ship.vy += Math.sin(ship.angle) * thrustPower * dt;
  } else if (thrustInput < 0) {
    ship.vx -= Math.cos(ship.angle) * reverseThrustPower * dt;
    ship.vy -= Math.sin(ship.angle) * reverseThrustPower * dt;
  }

  const drag = Math.pow(dragValue, dt * 60);
  ship.vx *= drag;
  ship.vy *= drag;

  const maxSpeed = speedBoostTimer > 0 ? SHIP_SPEED_BOOST_MAX_SPEED : SHIP_BASE_MAX_SPEED;
  const speed = Math.hypot(ship.vx, ship.vy);
  if (speed > maxSpeed) {
    const scale = maxSpeed / speed;
    ship.vx *= scale;
    ship.vy *= scale;
  }

  ship.x += ship.vx * dt;
  ship.y += ship.vy * dt;
  wrapPosition(ship);

  if (ship.invulnerable > 0) {
    ship.invulnerable = Math.max(0, ship.invulnerable - dt);
  }
}

function updateBullets(dt) {
  for (let i = bullets.length - 1; i >= 0; i -= 1) {
    const bullet = bullets[i];
    bullet.x += bullet.vx * dt;
    bullet.y += bullet.vy * dt;
    wrapPosition(bullet);
    bullet.life -= dt;

    if (bullet.life <= 0) {
      bullets.splice(i, 1);
    }
  }
}

function updateAsteroids(dt) {
  for (const asteroid of asteroids) {
    asteroid.x += asteroid.vx * dt;
    asteroid.y += asteroid.vy * dt;
    asteroid.rotation += asteroid.spin * dt;
    wrapPosition(asteroid);
  }
}

function applyPowerUp(powerUp) {
  if (powerUp.type === "shield") {
    shieldCharges += SHIELD_HITS_PER_PICKUP;
    return;
  }

  if (powerUp.type === "fire_rate") {
    fireRateBoostTimer = Math.max(fireRateBoostTimer, FIRE_RATE_DURATION);
    return;
  }

  if (powerUp.type === "life") {
    lives += 1;
    return;
  }

  speedBoostTimer = Math.max(speedBoostTimer, SPEED_BOOST_DURATION);
}

function updatePowerUpTimers(dt) {
  fireRateBoostTimer = Math.max(0, fireRateBoostTimer - dt);
  speedBoostTimer = Math.max(0, speedBoostTimer - dt);
}

function updatePowerUps(dt) {
  for (let i = powerUps.length - 1; i >= 0; i -= 1) {
    const powerUp = powerUps[i];
    powerUp.rotation += powerUp.spin * dt;
    powerUp.pulse += powerUp.pulseRate * dt;
  }

  if (shipDestroyed) {
    return;
  }

  for (let i = powerUps.length - 1; i >= 0; i -= 1) {
    const powerUp = powerUps[i];
    const dx = torusDelta(powerUp.x, ship.x, world.width);
    const dy = torusDelta(powerUp.y, ship.y, world.height);
    const hitDistance = ship.radius * 0.78 + powerUp.radius * 0.85;

    if (dx * dx + dy * dy <= hitDistance * hitDistance) {
      applyPowerUp(powerUp);
      debris.push({
        type: "ring",
        x: ship.x,
        y: ship.y,
        vx: ship.vx * 0.12,
        vy: ship.vy * 0.12,
        radius: ship.radius * 0.52,
        growth: 170,
        lineWidth: 2,
        life: 0.38,
        maxLife: 0.38,
        tint:
          powerUp.type === "shield"
            ? "126, 235, 255"
            : powerUp.type === "life"
              ? "255, 150, 178"
            : powerUp.type === "fire_rate"
              ? "255, 182, 108"
              : "172, 255, 176",
      });
      powerUps.splice(i, 1);
    }
  }
}

function updateSpawning(dt) {
  gameTime += dt;

  const asteroidRate = Math.min(
    ASTEROID_SPAWN_MAX_RATE,
    ASTEROID_SPAWN_BASE_RATE + ASTEROID_SPAWN_GROWTH_RATE * gameTime,
  );
  const enemyRate = Math.min(
    ENEMY_SPAWN_MAX_RATE,
    ENEMY_SPAWN_BASE_RATE + ENEMY_SPAWN_GROWTH_RATE * gameTime,
  );
  const powerUpRate = Math.min(
    POWERUP_SPAWN_MAX_RATE,
    POWERUP_SPAWN_BASE_RATE + POWERUP_SPAWN_GROWTH_RATE * gameTime,
  );
  const asteroidCap = Math.min(
    MAX_ASTEROIDS_CAP,
    BASE_MAX_ASTEROIDS + Math.floor(gameTime / 38),
  );
  const enemyCap = Math.min(
    MAX_ENEMIES_CAP,
    BASE_MAX_ENEMIES + Math.floor(gameTime / 55),
  );

  asteroidSpawnAccumulator += asteroidRate * dt;
  enemySpawnAccumulator += enemyRate * dt;
  powerUpSpawnAccumulator += powerUpRate * dt;

  while (asteroidSpawnAccumulator >= 1) {
    asteroidSpawnAccumulator -= 1;
    if (asteroids.length < asteroidCap) {
      spawnRandomAsteroid();
    }
  }

  while (enemySpawnAccumulator >= 1) {
    enemySpawnAccumulator -= 1;
    if (gameTime > 16 && enemies.length < enemyCap) {
      spawnRandomEnemy();
    }
  }

  if (asteroids.length < 5) {
    asteroidSpawnAccumulator = Math.max(asteroidSpawnAccumulator, 0.75);
  }

  if (enemies.length === 0 && gameTime > 42) {
    enemySpawnAccumulator = Math.max(enemySpawnAccumulator, 0.48);
  }

  while (powerUpSpawnAccumulator >= 1) {
    powerUpSpawnAccumulator -= 1;
    if (gameTime > 18 && powerUps.length < MAX_POWERUPS) {
      spawnRandomPowerUp();
    }
  }

  if (gameTime > 30 && powerUps.length === 0) {
    powerUpSpawnAccumulator = Math.max(powerUpSpawnAccumulator, 0.55);
  }
}

function updateEnemies(dt) {
  for (let i = 0; i < enemies.length; i += 1) {
    const enemy = enemies[i];
    enemy.wanderAngle += (Math.random() * 2 - 1) * 1.35 * dt;

    const toShipX = torusDelta(enemy.x, ship.x, world.width);
    const toShipY = torusDelta(enemy.y, ship.y, world.height);
    const distanceToShip = Math.hypot(toShipX, toShipY);
    const shipOnRadar =
      !shipDestroyed &&
      distanceToShip <= enemy.radarRange &&
      ship.invulnerable <= 0.8;
    enemy.alert = shipOnRadar;

    let steerX = Math.cos(enemy.wanderAngle) * ENEMY_WANDER_FORCE;
    let steerY = Math.sin(enemy.wanderAngle) * ENEMY_WANDER_FORCE;

    if (shipOnRadar) {
      const distanceRatio = 1 - distanceToShip / enemy.radarRange;
      const pursuitStrength =
        ENEMY_CHASE_FORCE *
        (0.5 + distanceRatio * 1.1) *
        enemy.aggression;
      const invDistance = 1 / Math.max(1, distanceToShip);
      steerX += toShipX * invDistance * pursuitStrength;
      steerY += toShipY * invDistance * pursuitStrength;
    } else {
      steerX += Math.cos(ambientTime * 0.55 + enemy.wanderAngle) * 0.32;
      steerY += Math.sin(ambientTime * 0.48 + enemy.wanderAngle) * 0.32;
    }

    for (const asteroid of asteroids) {
      const dx = torusDelta(enemy.x, asteroid.x, world.width);
      const dy = torusDelta(enemy.y, asteroid.y, world.height);
      const distance = Math.hypot(dx, dy);
      const safeDistance = asteroid.radius + enemy.radius + ENEMY_AVOID_DISTANCE;
      if (distance >= safeDistance) {
        continue;
      }

      const strength = ((safeDistance - distance) / safeDistance) * ENEMY_AVOID_FORCE;
      const invDistance = 1 / Math.max(1, distance);
      steerX -= dx * invDistance * strength;
      steerY -= dy * invDistance * strength;
    }

    for (let j = 0; j < enemies.length; j += 1) {
      if (j === i) {
        continue;
      }

      const other = enemies[j];
      const dx = torusDelta(enemy.x, other.x, world.width);
      const dy = torusDelta(enemy.y, other.y, world.height);
      const distance = Math.hypot(dx, dy);
      const safeDistance = enemy.radius + other.radius + 72;
      if (distance >= safeDistance) {
        continue;
      }

      const strength = ((safeDistance - distance) / safeDistance) * (ENEMY_AVOID_FORCE * 0.9);
      const invDistance = 1 / Math.max(1, distance);
      steerX -= dx * invDistance * strength;
      steerY -= dy * invDistance * strength;
    }

    if (!shipDestroyed && distanceToShip < enemy.radius + ship.radius + 100) {
      const invDistance = 1 / Math.max(1, distanceToShip);
      steerX -= toShipX * invDistance * 1.4;
      steerY -= toShipY * invDistance * 1.4;
    }

    const steerMagnitude = Math.hypot(steerX, steerY);
    if (steerMagnitude > 0) {
      steerX /= steerMagnitude;
      steerY /= steerMagnitude;
    }

    enemy.vx += steerX * ENEMY_ACCELERATION * dt;
    enemy.vy += steerY * ENEMY_ACCELERATION * dt;

    const drag = Math.pow(ENEMY_DRAG, dt * 60);
    enemy.vx *= drag;
    enemy.vy *= drag;

    const maxSpeed = shipOnRadar ? ENEMY_CHASE_SPEED : ENEMY_MAX_SPEED;
    const speed = Math.hypot(enemy.vx, enemy.vy);
    if (speed > maxSpeed) {
      const scale = maxSpeed / speed;
      enemy.vx *= scale;
      enemy.vy *= scale;
    }

    enemy.x += enemy.vx * dt;
    enemy.y += enemy.vy * dt;
    wrapPosition(enemy);

    const desiredHeading =
      speed > 14 ? Math.atan2(enemy.vy, enemy.vx) : enemy.wanderAngle;
    const headingDelta = shortestAngleDelta(enemy.angle, desiredHeading);
    enemy.angle += clamp(
      headingDelta,
      -ENEMY_TURN_RATE * dt,
      ENEMY_TURN_RATE * dt,
    );

    enemy.shootCooldown -= dt;
    if (shipOnRadar && enemy.shootCooldown <= 0) {
      const invDistance = 1 / Math.max(1, distanceToShip);
      const targetDirX = toShipX * invDistance;
      const targetDirY = toShipY * invDistance;
      const facingX = Math.cos(enemy.angle);
      const facingY = Math.sin(enemy.angle);
      const aimAlignment = facingX * targetDirX + facingY * targetDirY;

      if (aimAlignment > 0.72) {
        fireEnemyBullet(enemy, toShipX, toShipY, distanceToShip);
        enemy.shootCooldown =
          ENEMY_FIRE_COOLDOWN_MIN +
          Math.random() * (ENEMY_FIRE_COOLDOWN_MAX - ENEMY_FIRE_COOLDOWN_MIN);
      } else {
        enemy.shootCooldown = 0.2 + Math.random() * 0.3;
      }
    }
  }
}

function updateEnemyBullets(dt) {
  for (let i = enemyBullets.length - 1; i >= 0; i -= 1) {
    const projectile = enemyBullets[i];
    projectile.x += projectile.vx * dt;
    projectile.y += projectile.vy * dt;
    wrapPosition(projectile);
    projectile.life -= dt;

    if (projectile.life <= 0) {
      enemyBullets.splice(i, 1);
    }
  }
}

function updateDebris(dt) {
  for (let i = debris.length - 1; i >= 0; i -= 1) {
    const piece = debris[i];
    piece.x += piece.vx * dt;
    piece.y += piece.vy * dt;
    wrapPosition(piece);

    const drag = Math.pow(0.93, dt * 60);
    piece.vx *= drag;
    piece.vy *= drag;

    if (piece.type === "shard") {
      piece.rotation += piece.spin * dt;
    } else if (piece.type === "ring") {
      piece.radius += piece.growth * dt;
    } else {
      piece.radius += piece.growth * dt;
    }

    piece.life -= dt;

    if (piece.life <= 0) {
      debris.splice(i, 1);
    }
  }
}

function drawGalaxyBlob(galaxy, x, y, radius, alphaScale) {
  const glow = ctx.createRadialGradient(x, y, radius * 0.08, x, y, radius);
  const coreAlpha = galaxy.alpha * alphaScale;

  glow.addColorStop(0, `hsla(${galaxy.hue}, 96%, 74%, ${coreAlpha})`);
  glow.addColorStop(0.32, `hsla(${galaxy.hue + 18}, 90%, 62%, ${coreAlpha * 0.52})`);
  glow.addColorStop(0.75, `hsla(${galaxy.hue - 18}, 95%, 54%, ${coreAlpha * 0.16})`);
  glow.addColorStop(1, "rgba(0, 0, 0, 0)");

  ctx.fillStyle = glow;
  ctx.beginPath();
  ctx.arc(x, y, radius, 0, Math.PI * 2);
  ctx.fill();
}

function drawBackground() {
  const skyGradient = ctx.createLinearGradient(0, 0, 0, canvas.height);
  skyGradient.addColorStop(0, "#061022");
  skyGradient.addColorStop(0.55, "#040913");
  skyGradient.addColorStop(1, "#010206");
  ctx.fillStyle = skyGradient;
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.save();
  ctx.globalCompositeOperation = "screen";

  for (const galaxy of galaxies) {
    const pulse = 0.88 + 0.2 * Math.sin(galaxy.pulse);
    const radius = galaxy.radius * pulse;

    for (const dx of [-canvas.width, 0, canvas.width]) {
      for (const dy of [-canvas.height, 0, canvas.height]) {
        drawGalaxyBlob(galaxy, galaxy.x + dx, galaxy.y + dy, radius, 1);
      }
    }
  }

  ctx.restore();

  for (const layer of starLayers) {
    for (const star of layer.stars) {
      const x = wrapValue(star.x + layer.offsetX, canvas.width);
      const y = wrapValue(star.y + layer.offsetY, canvas.height);
      const twinkle = 0.74 + 0.26 * Math.sin(ambientTime * star.twinkle + star.phase);
      const alpha = star.alpha * twinkle;

      ctx.fillStyle = `rgba(${star.tint}, ${alpha})`;
      ctx.fillRect(x, y, star.size, star.size);

      if (star.size > 2.1) {
        ctx.fillStyle = `rgba(${star.tint}, ${alpha * 0.42})`;
        ctx.fillRect(x - 0.8, y + 0.4, star.size * 1.5, 0.5);
      }
    }
  }

  const vignette = ctx.createRadialGradient(
    canvas.width * 0.5,
    canvas.height * 0.45,
    Math.min(canvas.width, canvas.height) * 0.2,
    canvas.width * 0.5,
    canvas.height * 0.5,
    Math.max(canvas.width, canvas.height) * 0.72,
  );
  vignette.addColorStop(0, "rgba(0, 0, 0, 0)");
  vignette.addColorStop(1, "rgba(0, 0, 0, 0.34)");
  ctx.fillStyle = vignette;
  ctx.fillRect(0, 0, canvas.width, canvas.height);
}

function drawShip() {
  if (ship.invulnerable > 0 && Math.floor(ship.invulnerable * 12) % 2 === 0) {
    return;
  }

  const thrusting = isThrusting();
  const reverseThrusting = isReverseThrusting();
  const r = ship.radius;

  ctx.save();
  ctx.translate(canvas.width * 0.5 + camera.offsetX, canvas.height * 0.5 + camera.offsetY);
  ctx.rotate(ship.angle + Math.PI / 2);

  ctx.beginPath();
  ctx.moveTo(0, -r * 1.04);
  ctx.lineTo(r * 0.72, r * 0.66);
  ctx.lineTo(r * 0.28, r * 0.52);
  ctx.lineTo(0, r * 0.92);
  ctx.lineTo(-r * 0.28, r * 0.52);
  ctx.lineTo(-r * 0.72, r * 0.66);
  ctx.closePath();

  const hullGradient = ctx.createLinearGradient(0, -r, 0, r);
  hullGradient.addColorStop(0, "rgba(229, 239, 255, 0.98)");
  hullGradient.addColorStop(0.5, "rgba(159, 183, 214, 0.96)");
  hullGradient.addColorStop(1, "rgba(90, 110, 138, 0.97)");
  ctx.fillStyle = hullGradient;
  ctx.fill();

  ctx.strokeStyle = "rgba(48, 66, 88, 0.86)";
  ctx.lineWidth = 2.3;
  ctx.stroke();

  ctx.strokeStyle = "rgba(230, 242, 255, 0.75)";
  ctx.lineWidth = 1.05;
  ctx.stroke();

  ctx.fillStyle = "rgba(77, 104, 137, 0.75)";
  ctx.beginPath();
  ctx.moveTo(-r * 0.57, r * 0.33);
  ctx.lineTo(-r * 0.85, r * 0.78);
  ctx.lineTo(-r * 0.24, r * 0.66);
  ctx.closePath();
  ctx.fill();

  ctx.beginPath();
  ctx.moveTo(r * 0.57, r * 0.33);
  ctx.lineTo(r * 0.85, r * 0.78);
  ctx.lineTo(r * 0.24, r * 0.66);
  ctx.closePath();
  ctx.fill();

  ctx.strokeStyle = "rgba(211, 227, 245, 0.42)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(0, -r * 0.72);
  ctx.lineTo(0, r * 0.68);
  ctx.moveTo(-r * 0.24, r * 0.05);
  ctx.lineTo(r * 0.24, r * 0.05);
  ctx.moveTo(-r * 0.38, r * 0.35);
  ctx.lineTo(r * 0.38, r * 0.35);
  ctx.stroke();

  const canopy = ctx.createLinearGradient(0, -r * 0.58, 0, -r * 0.02);
  canopy.addColorStop(0, "rgba(178, 240, 255, 0.95)");
  canopy.addColorStop(1, "rgba(65, 131, 210, 0.7)");
  ctx.fillStyle = canopy;
  ctx.beginPath();
  ctx.ellipse(0, -r * 0.26, r * 0.2, r * 0.28, 0, 0, Math.PI * 2);
  ctx.fill();
  ctx.strokeStyle = "rgba(225, 248, 255, 0.75)";
  ctx.lineWidth = 0.9;
  ctx.stroke();

  ctx.fillStyle = "rgba(52, 74, 99, 0.85)";
  ctx.beginPath();
  ctx.moveTo(-r * 0.18, r * 0.72);
  ctx.lineTo(r * 0.18, r * 0.72);
  ctx.lineTo(r * 0.14, r * 0.96);
  ctx.lineTo(-r * 0.14, r * 0.96);
  ctx.closePath();
  ctx.fill();

  if (thrusting) {
    const flameLength = r * (0.95 + Math.random() * 0.62);
    const flameWidth = r * 0.36;
    const flameGradient = ctx.createLinearGradient(0, r * 0.7, 0, r + flameLength);
    flameGradient.addColorStop(0, "rgba(255, 248, 212, 0.95)");
    flameGradient.addColorStop(0.45, "rgba(255, 170, 70, 0.84)");
    flameGradient.addColorStop(1, "rgba(255, 104, 38, 0)");

    ctx.fillStyle = flameGradient;
    ctx.beginPath();
    ctx.moveTo(-flameWidth, r * 0.74);
    ctx.lineTo(0, r + flameLength);
    ctx.lineTo(flameWidth, r * 0.74);
    ctx.closePath();
    ctx.fill();

    ctx.fillStyle = "rgba(186, 244, 255, 0.72)";
    ctx.beginPath();
    ctx.moveTo(-flameWidth * 0.42, r * 0.76);
    ctx.lineTo(0, r + flameLength * 0.72);
    ctx.lineTo(flameWidth * 0.42, r * 0.76);
    ctx.closePath();
    ctx.fill();
  }

  if (reverseThrusting) {
    const reverseFlameLength = r * (0.6 + Math.random() * 0.4);
    const reverseFlameWidth = r * 0.24;
    const reverseGradient = ctx.createLinearGradient(
      0,
      -r * 0.68,
      0,
      -r - reverseFlameLength,
    );
    reverseGradient.addColorStop(0, "rgba(210, 248, 255, 0.9)");
    reverseGradient.addColorStop(0.55, "rgba(132, 216, 255, 0.7)");
    reverseGradient.addColorStop(1, "rgba(132, 216, 255, 0)");

    ctx.fillStyle = reverseGradient;
    ctx.beginPath();
    ctx.moveTo(-reverseFlameWidth, -r * 0.72);
    ctx.lineTo(0, -r - reverseFlameLength);
    ctx.lineTo(reverseFlameWidth, -r * 0.72);
    ctx.closePath();
    ctx.fill();
  }

  ctx.restore();
}

function traceAsteroidPath(asteroid, scale = 1) {
  ctx.beginPath();

  for (let i = 0; i < asteroid.offsets.length; i += 1) {
    const offset = asteroid.offsets[i];
    const angle = (i / asteroid.offsets.length) * Math.PI * 2;
    const r = asteroid.radius * offset * scale;
    const x = Math.cos(angle) * r;
    const y = Math.sin(angle) * r;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }

  ctx.closePath();
}

function drawAsteroid(asteroid) {
  const position = worldToScreen(asteroid.x, asteroid.y);
  if (!shouldRenderAt(position.x, position.y, asteroid.radius + 36)) {
    return;
  }

  ctx.save();
  ctx.translate(position.x, position.y);
  ctx.rotate(asteroid.rotation);

  traceAsteroidPath(asteroid);

  const surface = ctx.createLinearGradient(
    -asteroid.radius,
    -asteroid.radius,
    asteroid.radius,
    asteroid.radius,
  );
  surface.addColorStop(0, "rgba(204, 201, 196, 0.94)");
  surface.addColorStop(0.45, "rgba(140, 136, 132, 0.95)");
  surface.addColorStop(1, "rgba(92, 88, 84, 0.98)");
  ctx.fillStyle = surface;
  ctx.fill();

  ctx.save();
  ctx.clip();

  const shadow = ctx.createRadialGradient(
    -asteroid.radius * 0.2,
    -asteroid.radius * 0.4,
    asteroid.radius * 0.2,
    asteroid.radius * 0.3,
    asteroid.radius * 0.4,
    asteroid.radius * 1.45,
  );
  shadow.addColorStop(0, "rgba(0, 0, 0, 0)");
  shadow.addColorStop(1, "rgba(20, 18, 18, 0.48)");
  ctx.fillStyle = shadow;
  ctx.fillRect(
    -asteroid.radius * 1.4,
    -asteroid.radius * 1.4,
    asteroid.radius * 2.8,
    asteroid.radius * 2.8,
  );

  for (const facet of asteroid.facets) {
    const startAngle = facet.angle - facet.arc * 0.5;
    const endAngle = facet.angle + facet.arc * 0.5;
    const midAngle = facet.angle;

    ctx.fillStyle = `rgba(${facet.tone}, ${facet.alpha})`;
    ctx.beginPath();
    ctx.moveTo(
      Math.cos(startAngle) * asteroid.radius * facet.edgeA,
      Math.sin(startAngle) * asteroid.radius * facet.edgeA,
    );
    ctx.lineTo(
      Math.cos(endAngle) * asteroid.radius * facet.edgeB,
      Math.sin(endAngle) * asteroid.radius * facet.edgeB,
    );
    ctx.lineTo(
      Math.cos(midAngle) * asteroid.radius * facet.inner,
      Math.sin(midAngle) * asteroid.radius * facet.inner,
    );
    ctx.closePath();
    ctx.fill();
  }

  for (const ridge of asteroid.ridges) {
    const startX = Math.cos(ridge.startAngle) * asteroid.radius * ridge.startScale;
    const startY = Math.sin(ridge.startAngle) * asteroid.radius * ridge.startScale;
    const endX = Math.cos(ridge.endAngle) * asteroid.radius * ridge.endScale;
    const endY = Math.sin(ridge.endAngle) * asteroid.radius * ridge.endScale;

    ctx.strokeStyle = `rgba(222, 216, 208, ${ridge.alpha})`;
    ctx.lineWidth = ridge.width;
    ctx.beginPath();
    ctx.moveTo(startX, startY);
    ctx.lineTo(endX, endY);
    ctx.stroke();
  }

  traceAsteroidPath(asteroid, 0.78);
  ctx.strokeStyle = "rgba(28, 30, 36, 0.36)";
  ctx.lineWidth = 1.5;
  ctx.stroke();

  traceAsteroidPath(asteroid, 0.56);
  ctx.strokeStyle = "rgba(220, 215, 205, 0.13)";
  ctx.lineWidth = 1.2;
  ctx.stroke();

  ctx.restore();

  traceAsteroidPath(asteroid);
  ctx.strokeStyle = "rgba(58, 66, 78, 0.58)";
  ctx.lineWidth = 2.6;
  ctx.stroke();

  traceAsteroidPath(asteroid);
  ctx.strokeStyle = "rgba(198, 207, 219, 0.56)";
  ctx.lineWidth = 1.15;
  ctx.stroke();
  ctx.restore();
}

function drawEnemies() {
  for (const enemy of enemies) {
    const position = worldToScreen(enemy.x, enemy.y);
    if (!shouldRenderAt(position.x, position.y, enemy.radius + 30)) {
      continue;
    }

    ctx.save();
    ctx.translate(position.x, position.y);
    ctx.rotate(enemy.angle + Math.PI * 0.5);

    const hullGradient = ctx.createLinearGradient(0, -enemy.radius, 0, enemy.radius);
    if (enemy.alert) {
      hullGradient.addColorStop(0, "rgba(255, 222, 190, 0.96)");
      hullGradient.addColorStop(0.55, "rgba(252, 132, 84, 0.95)");
      hullGradient.addColorStop(1, "rgba(120, 48, 40, 0.96)");
    } else {
      hullGradient.addColorStop(0, "rgba(188, 230, 250, 0.95)");
      hullGradient.addColorStop(0.55, "rgba(96, 142, 176, 0.94)");
      hullGradient.addColorStop(1, "rgba(42, 61, 88, 0.96)");
    }

    ctx.beginPath();
    ctx.moveTo(0, -enemy.radius * 0.98);
    ctx.lineTo(enemy.radius * 0.84, enemy.radius * 0.62);
    ctx.lineTo(enemy.radius * 0.34, enemy.radius * 0.42);
    ctx.lineTo(0, enemy.radius * 0.95);
    ctx.lineTo(-enemy.radius * 0.34, enemy.radius * 0.42);
    ctx.lineTo(-enemy.radius * 0.84, enemy.radius * 0.62);
    ctx.closePath();
    ctx.fillStyle = hullGradient;
    ctx.fill();
    ctx.strokeStyle = enemy.alert
      ? "rgba(255, 225, 204, 0.74)"
      : "rgba(205, 229, 255, 0.68)";
    ctx.lineWidth = 1.3;
    ctx.stroke();

    ctx.strokeStyle = enemy.alert
      ? "rgba(255, 160, 122, 0.55)"
      : "rgba(146, 210, 248, 0.48)";
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, -enemy.radius * 0.64);
    ctx.lineTo(0, enemy.radius * 0.66);
    ctx.moveTo(-enemy.radius * 0.3, enemy.radius * 0.08);
    ctx.lineTo(enemy.radius * 0.3, enemy.radius * 0.08);
    ctx.stroke();

    ctx.fillStyle = enemy.alert
      ? "rgba(255, 217, 147, 0.95)"
      : "rgba(171, 235, 255, 0.92)";
    ctx.beginPath();
    ctx.ellipse(0, -enemy.radius * 0.18, enemy.radius * 0.18, enemy.radius * 0.24, 0, 0, Math.PI * 2);
    ctx.fill();

    ctx.restore();
  }
}

function drawEnemyBullets() {
  for (const projectile of enemyBullets) {
    const position = worldToScreen(projectile.x, projectile.y);
    if (!shouldRenderAt(position.x, position.y, 10)) {
      continue;
    }

    ctx.fillStyle = "rgba(255, 188, 130, 0.95)";
    ctx.beginPath();
    ctx.arc(position.x, position.y, projectile.radius, 0, Math.PI * 2);
    ctx.fill();
  }
}

function drawPowerUps() {
  for (const powerUp of powerUps) {
    const position = worldToScreen(powerUp.x, powerUp.y);
    if (!shouldRenderAt(position.x, position.y, 26)) {
      continue;
    }

    const pulse = 0.78 + 0.22 * Math.sin(powerUp.pulse);
    const radius = powerUp.radius * pulse;

    ctx.save();
    ctx.translate(position.x, position.y);
    ctx.rotate(powerUp.rotation);

    const glow = ctx.createRadialGradient(0, 0, radius * 0.25, 0, 0, radius * 1.75);
    if (powerUp.type === "shield") {
      glow.addColorStop(0, "rgba(122, 241, 255, 0.65)");
      glow.addColorStop(1, "rgba(122, 241, 255, 0)");
    } else if (powerUp.type === "life") {
      glow.addColorStop(0, "rgba(255, 152, 188, 0.65)");
      glow.addColorStop(1, "rgba(255, 152, 188, 0)");
    } else if (powerUp.type === "fire_rate") {
      glow.addColorStop(0, "rgba(255, 183, 112, 0.62)");
      glow.addColorStop(1, "rgba(255, 183, 112, 0)");
    } else {
      glow.addColorStop(0, "rgba(169, 255, 173, 0.62)");
      glow.addColorStop(1, "rgba(169, 255, 173, 0)");
    }

    ctx.fillStyle = glow;
    ctx.beginPath();
    ctx.arc(0, 0, radius * 1.75, 0, Math.PI * 2);
    ctx.fill();

    if (powerUp.type === "shield") {
      ctx.beginPath();
      ctx.moveTo(0, -radius * 0.95);
      ctx.lineTo(radius * 0.8, -radius * 0.18);
      ctx.lineTo(radius * 0.45, radius * 0.92);
      ctx.lineTo(-radius * 0.45, radius * 0.92);
      ctx.lineTo(-radius * 0.8, -radius * 0.18);
      ctx.closePath();
      ctx.fillStyle = "rgba(126, 240, 255, 0.45)";
      ctx.fill();
      ctx.strokeStyle = "rgba(190, 250, 255, 0.92)";
      ctx.lineWidth = 1.35;
      ctx.stroke();
    } else if (powerUp.type === "life") {
      ctx.strokeStyle = "rgba(255, 216, 232, 0.95)";
      ctx.lineWidth = 1.7;
      ctx.beginPath();
      ctx.moveTo(-radius * 0.6, 0);
      ctx.lineTo(radius * 0.6, 0);
      ctx.moveTo(0, -radius * 0.6);
      ctx.lineTo(0, radius * 0.6);
      ctx.stroke();
      ctx.strokeStyle = "rgba(255, 163, 198, 0.88)";
      ctx.lineWidth = 1;
      ctx.strokeRect(-radius * 0.74, -radius * 0.74, radius * 1.48, radius * 1.48);
    } else if (powerUp.type === "fire_rate") {
      ctx.strokeStyle = "rgba(255, 222, 190, 0.94)";
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      ctx.moveTo(-radius * 0.65, -radius * 0.58);
      ctx.lineTo(-radius * 0.05, -radius * 0.06);
      ctx.lineTo(-radius * 0.65, radius * 0.5);
      ctx.moveTo(0, -radius * 0.7);
      ctx.lineTo(radius * 0.6, -radius * 0.18);
      ctx.lineTo(0, radius * 0.38);
      ctx.moveTo(radius * 0.38, -radius * 0.52);
      ctx.lineTo(radius * 0.92, -radius * 0.08);
      ctx.lineTo(radius * 0.38, radius * 0.42);
      ctx.stroke();
    } else {
      ctx.strokeStyle = "rgba(207, 255, 209, 0.96)";
      ctx.lineWidth = 1.6;
      ctx.beginPath();
      ctx.moveTo(-radius * 0.78, radius * 0.24);
      ctx.lineTo(radius * 0.28, radius * 0.24);
      ctx.lineTo(radius * 0.28, radius * 0.62);
      ctx.lineTo(radius * 0.92, 0);
      ctx.lineTo(radius * 0.28, -radius * 0.62);
      ctx.lineTo(radius * 0.28, -radius * 0.24);
      ctx.lineTo(-radius * 0.78, -radius * 0.24);
      ctx.stroke();
    }

    ctx.restore();
  }
}

function drawBullets() {
  ctx.fillStyle = "#ffffff";

  for (const bullet of bullets) {
    const position = worldToScreen(bullet.x, bullet.y);
    if (!shouldRenderAt(position.x, position.y, 8)) {
      continue;
    }

    ctx.beginPath();
    ctx.arc(position.x, position.y, bullet.radius, 0, Math.PI * 2);
    ctx.fill();
  }
}

function drawDebris() {
  for (const piece of debris) {
    const position = worldToScreen(piece.x, piece.y);
    if (!shouldRenderAt(position.x, position.y, 40)) {
      continue;
    }

    const lifeRatio = piece.life / piece.maxLife;
    const alpha = Math.max(0, lifeRatio * lifeRatio);

    if (piece.type === "ring") {
      ctx.strokeStyle = `rgba(${piece.tint}, ${alpha * 0.74})`;
      ctx.lineWidth = piece.lineWidth * (0.8 + lifeRatio * 0.4);
      ctx.beginPath();
      ctx.arc(position.x, position.y, piece.radius, 0, Math.PI * 2);
      ctx.stroke();
      continue;
    }

    if (piece.type === "shard") {
      ctx.save();
      ctx.translate(position.x, position.y);
      ctx.rotate(piece.rotation);
      ctx.fillStyle = `rgba(${piece.tint}, ${alpha * (piece.glow ? 0.92 : 0.75)})`;
      ctx.fillRect(
        -piece.length * 0.5,
        -piece.width * 0.5,
        piece.length,
        piece.width,
      );
      ctx.strokeStyle = `rgba(252, 246, 238, ${alpha * (piece.glow ? 0.42 : 0.22)})`;
      ctx.lineWidth = 0.8;
      ctx.strokeRect(
        -piece.length * 0.5,
        -piece.width * 0.5,
        piece.length,
        piece.width,
      );
      ctx.restore();
      continue;
    }

    ctx.fillStyle = `rgba(${piece.tint}, ${alpha * 0.35})`;
    ctx.beginPath();
    ctx.arc(position.x, position.y, piece.radius, 0, Math.PI * 2);
    ctx.fill();
  }
}

function drawAsteroidHudIcon(x, y, size = 8) {
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(-0.35);
  ctx.beginPath();
  ctx.moveTo(0, -size);
  ctx.lineTo(size * 0.88, -size * 0.18);
  ctx.lineTo(size * 0.62, size * 0.82);
  ctx.lineTo(-size * 0.46, size * 0.92);
  ctx.lineTo(-size * 0.94, size * 0.1);
  ctx.closePath();
  ctx.fillStyle = "rgba(193, 196, 202, 0.9)";
  ctx.fill();
  ctx.strokeStyle = "rgba(230, 232, 238, 0.75)";
  ctx.lineWidth = 1;
  ctx.stroke();
  ctx.restore();
}

function drawEnemyHudIcon(x, y, size = 8) {
  ctx.save();
  ctx.translate(x, y);
  ctx.beginPath();
  ctx.moveTo(0, -size * 1.02);
  ctx.lineTo(size * 0.95, size * 0.72);
  ctx.lineTo(0, size * 0.35);
  ctx.lineTo(-size * 0.95, size * 0.72);
  ctx.closePath();
  ctx.fillStyle = "rgba(255, 151, 108, 0.92)";
  ctx.fill();
  ctx.strokeStyle = "rgba(255, 211, 186, 0.72)";
  ctx.lineWidth = 1;
  ctx.stroke();
  ctx.restore();
}

function drawShipHudIcon(x, y, size = 8, alpha = 1) {
  ctx.save();
  ctx.translate(x, y);
  ctx.globalAlpha *= alpha;
  ctx.beginPath();
  ctx.moveTo(0, -size * 1.08);
  ctx.lineTo(size * 0.88, size * 0.82);
  ctx.lineTo(0, size * 0.4);
  ctx.lineTo(-size * 0.88, size * 0.82);
  ctx.closePath();
  ctx.fillStyle = "rgba(208, 232, 255, 0.96)";
  ctx.fill();
  ctx.strokeStyle = "rgba(122, 153, 193, 0.82)";
  ctx.lineWidth = 1;
  ctx.stroke();
  ctx.restore();
}

function drawShieldHudIcon(x, y, size = 8, alpha = 1) {
  ctx.save();
  ctx.translate(x, y);
  ctx.globalAlpha *= alpha;
  ctx.beginPath();
  ctx.moveTo(0, -size * 1.06);
  ctx.lineTo(size * 0.82, -size * 0.2);
  ctx.lineTo(size * 0.48, size * 1.02);
  ctx.lineTo(-size * 0.48, size * 1.02);
  ctx.lineTo(-size * 0.82, -size * 0.2);
  ctx.closePath();
  ctx.fillStyle = "rgba(125, 233, 255, 0.45)";
  ctx.fill();
  ctx.strokeStyle = "rgba(188, 248, 255, 0.92)";
  ctx.lineWidth = 1;
  ctx.stroke();
  ctx.restore();
}

function drawFireRateHudIcon(x, y, size = 8, alpha = 1) {
  ctx.save();
  ctx.translate(x, y);
  ctx.globalAlpha *= alpha;
  ctx.strokeStyle = "rgba(255, 219, 183, 0.95)";
  ctx.lineWidth = 1.35;
  ctx.beginPath();
  ctx.moveTo(-size * 0.58, -size * 0.52);
  ctx.lineTo(-size * 0.04, -size * 0.08);
  ctx.lineTo(-size * 0.58, size * 0.42);
  ctx.moveTo(0, -size * 0.66);
  ctx.lineTo(size * 0.56, -size * 0.2);
  ctx.lineTo(0, size * 0.34);
  ctx.moveTo(size * 0.34, -size * 0.48);
  ctx.lineTo(size * 0.86, -size * 0.06);
  ctx.lineTo(size * 0.34, size * 0.4);
  ctx.stroke();
  ctx.restore();
}

function drawSpeedHudIcon(x, y, size = 8, alpha = 1) {
  ctx.save();
  ctx.translate(x, y);
  ctx.globalAlpha *= alpha;
  ctx.strokeStyle = "rgba(207, 255, 209, 0.96)";
  ctx.lineWidth = 1.45;
  ctx.beginPath();
  ctx.moveTo(-size * 0.84, size * 0.22);
  ctx.lineTo(size * 0.24, size * 0.22);
  ctx.lineTo(size * 0.24, size * 0.56);
  ctx.lineTo(size * 0.9, 0);
  ctx.lineTo(size * 0.24, -size * 0.56);
  ctx.lineTo(size * 0.24, -size * 0.22);
  ctx.lineTo(-size * 0.84, -size * 0.22);
  ctx.stroke();
  ctx.restore();
}

function drawPlayerStatusHud() {
  const rowY = 30;
  let cursor = canvas.width - 18;
  const groupGap = 14;

  const activeBoosts = [];
  if (fireRateBoostTimer > 0) {
    activeBoosts.push({ type: "fire_rate", timer: fireRateBoostTimer });
  }
  if (speedBoostTimer > 0) {
    activeBoosts.push({ type: "speed", timer: speedBoostTimer });
  }

  if (activeBoosts.length > 0) {
    for (let i = 0; i < activeBoosts.length; i += 1) {
      const boost = activeBoosts[i];
      const x = cursor - i * 38;

      ctx.fillStyle = "rgba(15, 23, 38, 0.62)";
      ctx.fillRect(x - 12, rowY - 12, 24, 24);
      ctx.strokeStyle = "rgba(154, 183, 214, 0.5)";
      ctx.lineWidth = 1;
      ctx.strokeRect(x - 11.5, rowY - 11.5, 23, 23);

      if (boost.type === "fire_rate") {
        drawFireRateHudIcon(x - 1, rowY - 2, 6.2);
      } else {
        drawSpeedHudIcon(x - 1, rowY - 2, 6.2);
      }

      ctx.fillStyle = "rgba(215, 233, 255, 0.88)";
      ctx.font = "700 9px monospace";
      ctx.textAlign = "center";
      ctx.fillText(`${Math.ceil(boost.timer)}`, x, rowY + 9);
    }
    cursor -= activeBoosts.length * 38 + groupGap;
  }

  if (shieldCharges > 0) {
    const maxShieldIcons = 8;
    const visibleShields = Math.min(shieldCharges, maxShieldIcons);
    for (let i = 0; i < visibleShields; i += 1) {
      drawShieldHudIcon(cursor - i * 14, rowY, 6.3);
    }

    if (shieldCharges > maxShieldIcons) {
      ctx.fillStyle = "rgba(195, 242, 255, 0.95)";
      ctx.font = "700 12px monospace";
      ctx.textAlign = "right";
      ctx.fillText(
        `x${shieldCharges}`,
        cursor - maxShieldIcons * 14 - 8,
        rowY + 4,
      );
      cursor -= maxShieldIcons * 14 + 46 + groupGap;
    } else {
      cursor -= visibleShields * 14 + groupGap;
    }
  }

  for (let i = 0; i < lives; i += 1) {
    drawShipHudIcon(cursor - i * 18, rowY, 7.8);
  }
}

function drawRadar() {
  const size = Math.min(RADAR_SIZE, Math.max(136, Math.min(canvas.width, canvas.height) * 0.3));
  const panelX = canvas.width - RADAR_PADDING - size;
  const panelY = canvas.height - RADAR_PADDING - size;
  const centerX = panelX + size * 0.5;
  const centerY = panelY + size * 0.5;
  const radius = size * 0.41;

  const gradient = ctx.createLinearGradient(panelX, panelY, panelX, panelY + size);
  gradient.addColorStop(0, "rgba(14, 22, 38, 0.68)");
  gradient.addColorStop(1, "rgba(8, 12, 20, 0.72)");
  ctx.fillStyle = gradient;
  ctx.fillRect(panelX, panelY, size, size);

  ctx.strokeStyle = "rgba(133, 164, 206, 0.42)";
  ctx.lineWidth = 1.5;
  ctx.strokeRect(panelX + 0.5, panelY + 0.5, size - 1, size - 1);

  ctx.beginPath();
  ctx.arc(centerX, centerY, radius, 0, Math.PI * 2);
  const radarFill = ctx.createRadialGradient(centerX, centerY, 0, centerX, centerY, radius);
  radarFill.addColorStop(0, "rgba(24, 54, 86, 0.5)");
  radarFill.addColorStop(1, "rgba(10, 20, 34, 0.24)");
  ctx.fillStyle = radarFill;
  ctx.fill();

  ctx.strokeStyle = "rgba(125, 183, 235, 0.32)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.arc(centerX, centerY, radius * 0.68, 0, Math.PI * 2);
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(centerX - radius, centerY);
  ctx.lineTo(centerX + radius, centerY);
  ctx.moveTo(centerX, centerY - radius);
  ctx.lineTo(centerX, centerY + radius);
  ctx.stroke();

  ctx.save();
  ctx.beginPath();
  ctx.arc(centerX, centerY, radius - 1, 0, Math.PI * 2);
  ctx.clip();

  for (const asteroid of asteroids) {
    const dx = torusDelta(ship.x, asteroid.x, world.width);
    const dy = torusDelta(ship.y, asteroid.y, world.height);
    const distance = Math.hypot(dx, dy);
    const factor =
      distance > RADAR_RANGE
        ? (radius * 0.98) / Math.max(distance, 1)
        : radius / RADAR_RANGE;
    const x = centerX + dx * factor;
    const y = centerY + dy * factor;
    ctx.fillStyle = "rgba(197, 200, 206, 0.85)";
    ctx.beginPath();
    ctx.arc(x, y, 1.8, 0, Math.PI * 2);
    ctx.fill();
  }

  for (const enemy of enemies) {
    const dx = torusDelta(ship.x, enemy.x, world.width);
    const dy = torusDelta(ship.y, enemy.y, world.height);
    const distance = Math.hypot(dx, dy);
    const factor =
      distance > RADAR_RANGE
        ? (radius * 0.98) / Math.max(distance, 1)
        : radius / RADAR_RANGE;
    const x = centerX + dx * factor;
    const y = centerY + dy * factor;
    ctx.fillStyle = enemy.alert
      ? "rgba(255, 186, 138, 0.95)"
      : "rgba(255, 158, 108, 0.86)";
    ctx.beginPath();
    ctx.arc(x, y, 2.2, 0, Math.PI * 2);
    ctx.fill();
  }

  ctx.restore();

  ctx.fillStyle = "rgba(166, 236, 255, 0.95)";
  ctx.beginPath();
  ctx.arc(centerX, centerY, 2.8, 0, Math.PI * 2);
  ctx.fill();
  ctx.strokeStyle = "rgba(212, 249, 255, 0.88)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.arc(centerX, centerY, 4.8, 0, Math.PI * 2);
  ctx.stroke();
}

function drawHud() {
  ctx.fillStyle = "#dbeafe";
  ctx.font = "700 24px monospace";
  ctx.textAlign = "center";
  ctx.fillText(`${score}`, canvas.width * 0.5, 34);

  if (screen === "playing") {
    const countsY = 30;
    const asteroidCountX = 18;
    const enemyCountX = 82;
    drawAsteroidHudIcon(asteroidCountX, countsY - 1, 6.5);
    drawEnemyHudIcon(enemyCountX, countsY - 1, 6.5);

    ctx.font = "700 15px monospace";
    ctx.fillStyle = "rgba(218, 233, 255, 0.95)";
    ctx.textAlign = "left";
    ctx.fillText(`${asteroids.length}`, asteroidCountX + 12, countsY + 4);
    ctx.fillText(`${enemies.length}`, enemyCountX + 12, countsY + 4);

    drawPlayerStatusHud();
    drawRadar();
  }
}

function drawWelcome() {
  const heading = gameOver ? "GAME OVER" : "ASTEROIDS";
  const subtitle = gameOver
    ? `Final score: ${score}`
    : mobileInput.enabled
      ? "Tap FIRE to Start"
      : "Press Space to Start";

  ctx.textAlign = "center";
  ctx.fillStyle = "#ffffff";
  ctx.font = "700 72px monospace";
  ctx.fillText(heading, canvas.width / 2, canvas.height * 0.34);

  ctx.font = "400 28px monospace";
  ctx.fillStyle = "#d8e6ff";
  ctx.fillText(subtitle, canvas.width / 2, canvas.height * 0.46);

  ctx.font = "400 22px monospace";
  ctx.fillStyle = "#9eb3d4";
  if (mobileInput.enabled) {
    ctx.fillText("Drag the left control circle to steer", canvas.width / 2, canvas.height * 0.6);
    ctx.fillText("Top = thrust, bottom = reverse", canvas.width / 2, canvas.height * 0.67);
    ctx.fillText("Diagonals combine turn + thrust", canvas.width / 2, canvas.height * 0.74);
  } else {
    ctx.fillText(
      "Rotate: Left / Right (or A / D)",
      canvas.width / 2,
      canvas.height * 0.57,
    );
    ctx.fillText("Thrust: Up (or W)", canvas.width / 2, canvas.height * 0.63);
    ctx.fillText("Reverse Thrust: Down (or S)", canvas.width / 2, canvas.height * 0.69);
    ctx.fillText("Shoot: Space", canvas.width / 2, canvas.height * 0.75);
  }
}

function updateGame(dt) {
  if (screen !== "playing") {
    return;
  }

  const thrusting = isThrusting();
  const reverseThrusting = isReverseThrusting();
  const thrustInput = (thrusting ? 1 : 0) - (reverseThrusting ? 1 : 0);
  updatePowerUpTimers(dt);
  updateSpawning(dt);
  shootTimer = Math.max(0, shootTimer - dt);
  if (!shipDestroyed && mobileInput.enabled && hasTouchAction("fire")) {
    fireBullet();
  }
  if (!shipDestroyed) {
    updateShip(dt, thrustInput);
  } else {
    shipExplosionTimer = Math.max(0, shipExplosionTimer - dt);

    if (shipExplosionTimer === 0) {
      if (pendingGameOver) {
        pendingGameOver = false;
        shipDestroyed = false;
        endGame();
        return;
      }

      if (pendingRespawn) {
        pendingRespawn = false;
        shipDestroyed = false;
        resetShip();
        ship.invulnerable = 2;
      }
    }
  }
  updateAsteroids(dt);
  updateEnemies(dt);
  updateBullets(dt);
  updateEnemyBullets(dt);
  updatePowerUps(dt);
  updateDebris(dt);
  checkCollisions();
  updateCamera(dt, thrustInput);
}

function render() {
  drawBackground();

  if (screen === "playing") {
    for (const asteroid of asteroids) {
      drawAsteroid(asteroid);
    }
    drawPowerUps();
    drawEnemies();
    drawDebris();
    drawBullets();
    drawEnemyBullets();
    if (!shipDestroyed) {
      drawShip();
    }
  } else {
    drawWelcome();
  }

  drawHud();
}

function loop(timestamp) {
  if (!lastTimestamp) {
    lastTimestamp = timestamp;
  }

  const dt = Math.min((timestamp - lastTimestamp) / 1000, 0.033);
  lastTimestamp = timestamp;

  updateBackground(dt);
  updateGame(dt);
  render();
  requestAnimationFrame(loop);
}

document.addEventListener("selectstart", (event) => {
  event.preventDefault();
});

window.addEventListener(
  "dblclick",
  (event) => {
    event.preventDefault();
  },
  { passive: false },
);

window.addEventListener(
  "touchstart",
  (event) => {
    if (event.touches.length > 1) {
      event.preventDefault();
    }
  },
  { passive: false },
);

window.addEventListener(
  "touchend",
  (event) => {
    const now = performance.now();
    if (now - lastTouchEndTime < 320) {
      event.preventDefault();
    }
    lastTouchEndTime = now;
  },
  { passive: false },
);

window.addEventListener("keydown", (event) => {
  const preventKeys = ["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Space"];
  if (preventKeys.includes(event.code)) {
    event.preventDefault();
  }

  keys.add(event.code);

  if (event.code === "Space" && !event.repeat) {
    if (screen === "playing") {
      fireBullet();
    } else {
      startGame();
    }
  }
});

window.addEventListener("keyup", (event) => {
  keys.delete(event.code);
});

window.addEventListener("blur", () => {
  keys.clear();
  clearTouchActions();
});

document.addEventListener("visibilitychange", () => {
  if (document.hidden) {
    keys.clear();
    clearTouchActions();
  }
});

window.addEventListener("resize", resizeCanvas);

setupMobileControls();
resizeCanvas();
render();
requestAnimationFrame(loop);
