document.addEventListener('DOMContentLoaded', () => {
    let audioContext, analyser, source;
    const audioControl = document.getElementById('audio-control');
    const audio = document.getElementById('audio');
    const scanningOverlay = document.getElementById('scanning-overlay');
    const scene = document.querySelector('a-scene');
    const sphere = document.getElementById('visualSphere');
    const model = document.getElementById('base-entity');
    const equalizerContainer = document.getElementById('equalizer-container');
    const mindarTarget = document.querySelector('[mindar-image-target]');
    const lyricsOverlay = document.getElementById('lyrics-overlay');
    const toggleLyricsButton = document.getElementById('toggle-lyrics');
    const websiteButton = document.getElementById('website-button');

    //音楽再生バー
    const seekBar = document.getElementById('seek-bar');
    const currentTimeDisplay = document.getElementById('current-time');
    const durationDisplay = document.getElementById('duration');

    const FFT_SIZE = 256;
    const numBars = 32; // 固定のバーの数に変更
    let bars = [];
    let isLyricsVisible = false;

    // 3Dパーティクルシステムの定数（視認性向上のため最適化）
    const PARTICLE_COUNT = 50000; // 密度を高めて視認性向上
    const SHAPE_STABLE_TIME = 4000; // 4秒
    const MORPHING_TIME = 2000; // 2秒
    const ANIMATION_CYCLE = SHAPE_STABLE_TIME + MORPHING_TIME; // 6秒

    // パーティクルシステムの変数
    let particleSystem = null;
    let particleGeometry = null;
    let particleMaterial = null;
    let particlePositions = null;
    let particleColors = null;

    // 形状データ（事前計算済み）
    let torusPositions = null;
    let spherePositions = null;
    let lissajousPositions = null;
    let dnaHelixPositions = null;
    let fractalCubePositions = null;
    let galaxySpiralPositions = null;
    let waveFormPositions = null;
    let supernovaPositions = null;
    let quantumFieldPositions = null;
    let trainWheelPositions = null;
    let railTrackPositions = null;
    let shiningStarPositions = null;

    // アニメーション状態
    let currentShape = 'TRAIN_WHEEL'; // 歌詞に合わせて車輪からスタート
    let nextShape = 'RAIL_TRACK';
    let morphProgress = 0;
    let animationStartTime = 0;
    let isStable = true;

    // リッチアニメーション状態
    let globalRotation = { x: 0, y: 0, z: 0 };
    let pulsePhase = 0;
    let colorWavePhase = 0;
    let rotationSpeed = 0.008;

    // パフォーマンス最適化用変数
    let lastUpdateTime = 0;
    const UPDATE_FREQUENCY = 16; // 60FPS相当
    let frameSkipCounter = 0;
    const MAX_FRAME_SKIP = 2; // 最大2フレームまでスキップ可能

    // パフォーマンス監視用変数
    let frameCount = 0;
    let lastFpsTime = 0;
    let currentFps = 60;
    let performanceLevel = 'high'; // 'high', 'medium', 'low'

    // オーディオ連動用変数
    let currentAudioLevel = 0;
    let audioLevelSmooth = 0;
    let bassPeak = 0; // ピーク検出用

    // 歌詞の初期状態設定
    isLyricsVisible = false;
    lyricsOverlay.style.display = 'none';

    // 3D形状の数学的定義と事前計算
    function generateTorusPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const R = 1.2; // 主半径 (2 → 1.2に縮小)
        const r = 0.48; // 管半径 (0.8 → 0.48に縮小)

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const u = Math.random() * Math.PI * 2;
            const v = Math.random() * Math.PI * 2;

            const x = (R + r * Math.cos(v)) * Math.cos(u);
            const y = (R + r * Math.cos(v)) * Math.sin(u);
            const z = r * Math.sin(v);

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }

        return positions;
    }

    function generateSpherePositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const R = 1.32; // 2.2 → 1.32に縮小

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const lat = Math.random() * Math.PI;
            const lon = Math.random() * Math.PI * 2;

            const x = R * Math.sin(lat) * Math.cos(lon);
            const y = R * Math.sin(lat) * Math.sin(lon);
            const z = R * Math.cos(lat);

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }

        return positions;
    }

    function generateLissajousPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const a = 3, b = 5, c = 7;
        const A = 1.2, B = 1.2, C = 1.2; // 2 → 1.2に縮小
        const delta1 = Math.PI / 2, delta2 = Math.PI / 4;
        const thicknessRadius = 0.08;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const t = (i / PARTICLE_COUNT) * Math.PI * 4;

            const baseX = A * Math.sin(a * t + delta1);
            const baseY = B * Math.sin(b * t);
            const baseZ = C * Math.sin(c * t + delta2);

            const offsetAngle = Math.random() * Math.PI * 2;
            const offsetRadius = Math.random() * thicknessRadius;

            const offsetX = Math.cos(offsetAngle) * offsetRadius;
            const offsetY = Math.sin(offsetAngle) * offsetRadius;

            positions[i * 3] = baseX + offsetX;
            positions[i * 3 + 1] = baseY + offsetY;
            positions[i * 3 + 2] = baseZ;
        }

        return positions;
    }

    function generateDnaHelixPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const R = 0.9; // 1.5 → 0.9に縮小
        const height = 2.4; // 4 → 2.4に縮小
        const turns = 3;
        const thicknessRadius = 0.05;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const t = (i / PARTICLE_COUNT) * turns * Math.PI * 2;
            const y = (i / PARTICLE_COUNT) * height - height / 2;

            const strand = Math.floor(i / (PARTICLE_COUNT / 2));
            const offset = strand * Math.PI;

            const baseX = R * Math.cos(t + offset);
            const baseZ = R * Math.sin(t + offset);

            const offsetAngle = Math.random() * Math.PI * 2;
            const offsetRadius = Math.random() * thicknessRadius;
            const offsetX = Math.cos(offsetAngle) * offsetRadius;
            const offsetZ = Math.sin(offsetAngle) * offsetRadius;

            positions[i * 3] = baseX + offsetX;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = baseZ + offsetZ;
        }

        return positions;
    }

    function generateFractalCubePositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const size = 1.2; // 2.0 → 1.2に縮小
        const levels = 3;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            let x = 0, y = 0, z = 0;
            let currentSize = size;

            for (let level = 0; level < levels; level++) {
                const subdivide = Math.pow(2, level);
                const localSize = currentSize / subdivide;

                const localX = (Math.random() - 0.5) * localSize;
                const localY = (Math.random() - 0.5) * localSize;
                const localZ = (Math.random() - 0.5) * localSize;

                x += localX;
                y += localY;
                z += localZ;

                currentSize *= 0.5;
            }

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }

        return positions;
    }

    function generateGalaxySpiralPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const arms = 3;
        const maxRadius = 1.8; // 3.0 → 1.8に縮小
        const pitch = 0.3;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const armIndex = i % arms;
            const t = (i / PARTICLE_COUNT) * Math.PI * 4;
            const radius = (i / PARTICLE_COUNT) * maxRadius;

            const angle = t + (armIndex * Math.PI * 2 / arms) + (radius * pitch);

            const x = radius * Math.cos(angle);
            const z = radius * Math.sin(angle);

            const y = (Math.random() - 0.5) * 0.2 * radius;

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }

        return positions;
    }

    function generateWaveFormPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const width = 2.4; // 4.0 → 2.4に縮小
        const amplitude = 0.9; // 1.5 → 0.9に縮小
        const frequency = 2.0;
        const waveCount = 5;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const t = (i / PARTICLE_COUNT) * Math.PI * 2 * waveCount;
            const x = (i / PARTICLE_COUNT) * width - width / 2;

            const wave1 = Math.sin(t) * amplitude;
            const wave2 = Math.sin(t * 2 + Math.PI / 3) * amplitude * 0.5;
            const wave3 = Math.sin(t * 3 + Math.PI / 6) * amplitude * 0.25;

            const y = wave1 + wave2 + wave3;

            const z = Math.sin(t * frequency) * 0.3;

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }

        return positions;
    }

    function generateSupernovaPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const coreRadius = 0.3;
        const rayLength = 2.5;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            // 30%はコア、70%は放射状の線
            if (Math.random() < 0.3) {
                // コア（球体）
                const theta = Math.random() * Math.PI * 2;
                const phi = Math.acos(2 * Math.random() - 1);
                const r = Math.pow(Math.random(), 1 / 3) * coreRadius;

                positions[i * 3] = r * Math.sin(phi) * Math.cos(theta);
                positions[i * 3 + 1] = r * Math.sin(phi) * Math.sin(theta);
                positions[i * 3 + 2] = r * Math.cos(phi);
            } else {
                // 放射線（バースト）
                const theta = Math.random() * Math.PI * 2;
                const phi = Math.acos(2 * Math.random() - 1);
                // 中心に集中しつつ、外側へ伸びる分布
                const r = coreRadius + Math.pow(Math.random(), 4) * rayLength;

                positions[i * 3] = r * Math.sin(phi) * Math.cos(theta);
                positions[i * 3 + 1] = r * Math.sin(phi) * Math.sin(theta);
                positions[i * 3 + 2] = r * Math.cos(phi);
            }
        }
        return positions;
    }

    function generateQuantumFieldPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const size = 2.0;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            // ランダムな雲のような分布だが、数式的な美しさを持たせる
            // ストレンジアトラクタのような軌跡
            let x = (Math.random() - 0.5) * size;
            let y = (Math.random() - 0.5) * size;
            let z = (Math.random() - 0.5) * size;

            // クリフォードアトラクタ風の変形
            const a = 1.5, b = 1.5, c = 1.5, d = 0.8;
            const xn = Math.sin(a * y) + c * Math.cos(a * x);
            const yn = Math.sin(b * x) + d * Math.cos(b * y);
            const zn = Math.sin(z); // 簡易化

            // 範囲を正規化して適用
            positions[i * 3] = xn * 0.8;
            positions[i * 3 + 1] = yn * 0.8;
            positions[i * 3 + 2] = zn * 0.8 + (Math.random() - 0.5) * 0.5;
        }
        return positions;
    }

    function generateKleinBottlePositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const scale = 0.4; // サイズ調整

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const u = (i / PARTICLE_COUNT) * Math.PI * 2; // 0 to 2PI
            const v = Math.random() * Math.PI * 2; // 0 to 2PI

            // クラインの壺のパラメトリック方程式
            const r = 4 * (1 - Math.cos(u) / 2);
            let x, y, z;

            if (u < Math.PI) {
                x = 6 * Math.cos(u) * (1 + Math.sin(u)) + r * Math.cos(u) * Math.cos(v);
                y = 16 * Math.sin(u) + r * Math.sin(u) * Math.cos(v);
            } else {
                x = 6 * Math.cos(u) * (1 + Math.sin(u)) + r * Math.cos(v + Math.PI);
                y = 16 * Math.sin(u);
            }
            z = r * Math.sin(v);

            positions[i * 3] = x * scale * 0.1;
            positions[i * 3 + 1] = y * scale * 0.1 - 0.5; // 中心位置調整
            positions[i * 3 + 2] = z * scale * 0.1;
        }
        return positions;
    }

    function generateTrainWheelPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const rimRadius = 1.5;
        const hubRadius = 0.3;
        const spokes = 12;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const r = Math.random();
            let x, y, z;

            if (r < 0.6) { // リム（外枠）
                const angle = Math.random() * Math.PI * 2;
                const width = (Math.random() - 0.5) * 0.2;
                const thickness = (Math.random() - 0.5) * 0.2;
                x = (rimRadius + thickness) * Math.cos(angle);
                y = (rimRadius + thickness) * Math.sin(angle);
                z = width;
            } else if (r < 0.8) { // スポーク
                const spokeIndex = Math.floor(Math.random() * spokes);
                const angle = (spokeIndex / spokes) * Math.PI * 2;
                const dist = Math.random() * rimRadius;
                const spread = (Math.random() - 0.5) * 0.1;
                x = dist * Math.cos(angle) + spread;
                y = dist * Math.sin(angle) + spread;
                z = (Math.random() - 0.5) * 0.1;
            } else { // ハブ（中心）
                const angle = Math.random() * Math.PI * 2;
                const dist = Math.random() * hubRadius;
                x = dist * Math.cos(angle);
                y = dist * Math.sin(angle);
                z = (Math.random() - 0.5) * 0.5;
            }

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }
        return positions;
    }

    function generateRailTrackPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const length = 4.0;
        const width = 1.0;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            const t = Math.random(); // 0 to 1 along the track
            const z = (t - 0.5) * length;

            let x, y;

            if (Math.random() < 0.7) { // レール
                const side = Math.random() < 0.5 ? -1 : 1;
                x = side * width * 0.5 + (Math.random() - 0.5) * 0.1;
                y = (Math.random() - 0.5) * 0.1;
            } else { // 枕木
                // 一定間隔で配置
                const sleeperIndex = Math.floor(t * 20);
                const sleeperZ = (sleeperIndex / 20 - 0.5) * length;
                // zをsleeperZに近づける
                const localZ = z - sleeperZ;
                if (Math.abs(localZ) < 0.05) {
                    x = (Math.random() - 0.5) * (width + 0.4);
                    y = -0.1 + (Math.random() - 0.5) * 0.1;
                } else {
                    // レールに戻す
                    const side = Math.random() < 0.5 ? -1 : 1;
                    x = side * width * 0.5 + (Math.random() - 0.5) * 0.1;
                    y = (Math.random() - 0.5) * 0.1;
                }
            }

            // トンネル効果のために少し湾曲させる
            y += Math.sin(t * Math.PI) * 0.5;

            positions[i * 3] = x;
            positions[i * 3 + 1] = y;
            positions[i * 3 + 2] = z;
        }
        return positions;
    }

    function generateShiningStarPositions() {
        const positions = new Float32Array(PARTICLE_COUNT * 3);
        const points = 5;
        const outerRadius = 1.5;
        const innerRadius = 0.6;

        for (let i = 0; i < PARTICLE_COUNT; i++) {
            // 星型の中身を埋める
            const angle = Math.random() * Math.PI * 2;
            // 星の境界計算
            const step = Math.PI / points;
            // 簡易的な星型判定は難しいので、放射状の腕を作る

            if (Math.random() < 0.2) {
                // 中心部の輝き
                const r = Math.random() * innerRadius;
                const theta = Math.random() * Math.PI * 2;
                const phi = Math.random() * Math.PI;
                positions[i * 3] = r * Math.sin(phi) * Math.cos(theta);
                positions[i * 3 + 1] = r * Math.sin(phi) * Math.sin(theta);
                positions[i * 3 + 2] = r * Math.cos(phi);
            } else {
                // 5つの腕
                const arm = Math.floor(Math.random() * points);
                const armAngle = (arm / points) * Math.PI * 2 - (Math.PI / 2); // 上向き開始

                const dist = Math.random() * outerRadius;
                // 腕の太さ
                const spread = (1.0 - (dist / outerRadius)) * 0.3;

                const localX = (Math.random() - 0.5) * spread;
                const localY = dist;
                const localZ = (Math.random() - 0.5) * spread;

                // 回転
                const x = localX * Math.cos(armAngle) - localY * Math.sin(armAngle);
                const y = localX * Math.sin(armAngle) + localY * Math.cos(armAngle);
                const z = localZ;

                positions[i * 3] = x;
                positions[i * 3 + 1] = y;
                positions[i * 3 + 2] = z;
            }
        }
        return positions;
    }

    // リンクボタンのイベントリスナー
    websiteButton.addEventListener('click', () => {
        window.open('https://www.instagram.com/techconnect.em/', '_blank');
    });

    // 再生時間を整形する関数
    function formatTime(seconds) {
        const mins = Math.floor(seconds / 60);
        const secs = Math.floor(seconds % 60);

        // 負の時間を考慮
        const absMins = Math.abs(mins);
        const absSecs = Math.abs(secs);

        const formattedMins = String(absMins).padStart(0, '0');
        const formattedSecs = String(absSecs).padStart(2, '0');
        return `${mins < 0 ? '-' : ''}${formattedMins}:${formattedSecs}`;
    }

    // イベントリスナー: メタデータがロードされたとき
    audio.addEventListener('loadedmetadata', () => {
        if (isNaN(audio.duration)) {
            console.warn("audio.duration is NaN. Trying again...");
            return;
        }
        const durationInSeconds = audio.duration;
        seekBar.max = durationInSeconds;
        durationDisplay.textContent = formatTime(durationInSeconds); // durationを初期化
    });

    // イベントリスナー: 再生時間が更新されたとき
    audio.addEventListener('timeupdate', () => {
        currentTimeDisplay.textContent = formatTime(audio.currentTime);
        seekBar.value = audio.currentTime;
        // 経過時間から残りの時間を計算して表示
        const timeLeft = audio.duration - audio.currentTime;
        durationDisplay.textContent = formatTime(timeLeft);
    });

    // イベントリスナー: seek barが変更されたとき
    seekBar.addEventListener('input', () => {
        audio.currentTime = seekBar.value;
        currentTimeDisplay.textContent = formatTime(audio.currentTime);
    });

    // イベントリスナー: 楽曲の再生が終わったとき
    audio.addEventListener('ended', () => {
        audioControl.querySelector('i').className = 'fas fa-play';
    });


    // 音声解析の初期化
    async function initAudioAnalyser() {
        try {
            audioContext = new (window.AudioContext || window.webkitAudioContext)();
            await audioContext.resume();

            analyser = audioContext.createAnalyser();
            analyser.fftSize = FFT_SIZE;
            analyser.smoothingTimeConstant = 0.85;
            source = audioContext.createMediaElementSource(audio);
            source.connect(analyser);
            analyser.connect(audioContext.destination);

            // イコライザーバーの初期化
            try {
                for (let i = 0; i < numBars; i++) {
                    const bar = document.createElement('a-entity');
                    bar.setAttribute('geometry', `primitive: box; width: 0.02; height: 0.1; depth: 0.02`);
                    bar.setAttribute('material', `color: yellow`);
                    equalizerContainer.appendChild(bar);
                    bars.push(bar);
                }
                console.log('Equalizer bars initialized successfully.');
            } catch (error) {
                console.error('Error initializing equalizer bars:', error);
            }


            return true;
        } catch (error) {
            console.error('Audio analyser initialization error:', error);
            return false;
        }
    }

    // 音声データの解析と視覚化
    AFRAME.registerComponent('audio-visualizer', {
        init: function () {
            this.barWidth = 0.02;
            this.barColor = 'yellow';
            this.equalizerRadius = 1.1;
            this.smoothing = 0.3;
            this.barHeights = new Array(numBars).fill(0); // スムージング用の配列
            console.log('Audio visualizer component initialized.');
        },
        tick: function () {
            if (analyser && !audio.paused) {
                const freqByteData = new Uint8Array(analyser.frequencyBinCount);
                analyser.getByteFrequencyData(freqByteData);

                // スフィアのスケールを変更
                let avgScale = 0;
                for (let i = 0; i < freqByteData.length; i++) {
                    avgScale += freqByteData[i];
                }
                avgScale /= freqByteData.length;
                const scale = 1 + (avgScale / 255) * 0.5;
                this.el.object3D.scale.set(scale, scale, scale);

                // イコライザーバーの更新
                this.updateEqualizerBars(freqByteData);

                // パーティクル用オーディオレベル計算 (低音域重視 - バスドラムのみを狙う)
                let sum = 0;
                // FFT_SIZE=256, binCount=128, 44.1kHzの場合、1binは約172Hz
                // 3binまで取れば ~516Hz。これでバスドラムとベースの基音をカバー
                const bassRange = 3;
                for (let i = 0; i < bassRange; i++) {
                    sum += freqByteData[i];
                }
                // 平均化して0-1に正規化
                const rawLevel = (sum / bassRange) / 255;

                // しきい値処理（ノイズカット）
                const threshold = 0.4;
                const clippedLevel = Math.max(0, rawLevel - threshold) * (1 / (1 - threshold));

                // ピーク検出と減衰（パンチ感を出す）
                if (clippedLevel > bassPeak) {
                    bassPeak = clippedLevel; // アタック：即座に反応
                } else {
                    bassPeak *= 0.9; // ディケイ：徐々に減衰
                }

                currentAudioLevel = bassPeak;
            }
        },
        updateEqualizerBars: function (freqByteData) {
            try {
                const targetPosition = mindarTarget.object3D.position;
                const radius = parseFloat(sphere.getAttribute('radius')) * this.equalizerRadius;
                const sphereBottomY = targetPosition.y - parseFloat(sphere.getAttribute('radius'));

                for (let i = 0; i < numBars; i++) {
                    const bar = bars[i];

                    if (!bar) {
                        console.error('bar is null or undefined:', i, bars);
                        continue;
                    }
                    // 使用する周波数データを選択（高周波数帯域をカット）
                    const freqIndex = Math.floor((i / numBars) * (FFT_SIZE / 2));
                    const freqSum = freqByteData[freqIndex] || 0;
                    let barHeight = (freqSum / 255) * 1.5;
                    barHeight = Math.max(0.1, barHeight); // 最小値を設定

                    // スムージング処理
                    this.barHeights[i] = this.barHeights[i] + (barHeight - this.barHeights[i]) * this.smoothing;

                    let angle = 0;
                    if (numBars > 1) {
                        angle = (i / (numBars - 1)) * Math.PI - (Math.PI / 2);
                    }
                    const x = Math.cos(angle - Math.PI / 2) * radius;
                    const z = Math.sin(angle - Math.PI / 2) * radius;
                    const y = sphereBottomY + this.barHeights[i] / 2;

                    bar.setAttribute('position', `${targetPosition.x + x} ${y} ${targetPosition.z + z}`);
                    bar.setAttribute('geometry', `primitive: box; width: ${this.barWidth}; height: ${this.barHeights[i]}; depth: ${this.barWidth}`);
                    bar.setAttribute('rotation', `0 ${-angle * 180 / Math.PI - 90} 0`);
                }
            } catch (error) {
                console.error('Error during equalizer animation:', error);
            }
        }
    });

    sphere.setAttribute('audio-visualizer', '');

    let isTargetFound = false;

    scene.addEventListener('targetFound', () => {
        isTargetFound = true;
        scanningOverlay.classList.add('fade-out');
        // 歌詞表示は手動制御のまま維持
    });

    scene.addEventListener('targetLost', () => {
        isTargetFound = false;
        scanningOverlay.classList.remove('fade-out');
        // 歌詞表示は手動制御のまま維持
    });

    scene.addEventListener('error', (e) => {
        console.error('A-Frame scene error:', e);
    });

    audio.addEventListener('play', updateAudioButton);
    audio.addEventListener('pause', updateAudioButton);


    //音楽再生、歌詞表示、Webサイト移動などのイベントリスナーを定義
    websiteButton.addEventListener('click', () => {
        window.open('https://www.instagram.com/techconnect.em/', '_blank');
    });

    toggleLyricsButton.addEventListener('click', (event) => {
        event.preventDefault();
        event.stopPropagation();

        console.log('歌詞ボタンがクリックされました');
        console.log('現在のisLyricsVisible:', isLyricsVisible);

        isLyricsVisible = !isLyricsVisible;

        // 歌詞表示とbodyスクロール制御
        if (isLyricsVisible) {
            lyricsOverlay.style.display = 'flex';
            document.body.classList.add('lyrics-visible');
            console.log('歌詞を表示に設定');
        } else {
            lyricsOverlay.style.display = 'none';
            document.body.classList.remove('lyrics-visible');
            console.log('歌詞を非表示に設定');
        }

        // 確認のため最終状態をログ出力
        setTimeout(() => {
            console.log('最終的なdisplayプロパティ:', getComputedStyle(lyricsOverlay).display);
        }, 100);

        updateLyricsButton();
    });

    function updateLyricsButton() {
        const icon = toggleLyricsButton.querySelector('i');
        icon.className = isLyricsVisible ? 'fas fa-times' : 'fas fa-align-justify';
    }

    audioControl.addEventListener('click', async () => {
        try {
            if (audio.paused) {
                await audio.play();
                await audioContext.resume();
            } else {
                audio.pause();
            }
            updateAudioButton();
        } catch (error) {
            console.error('Audio control error:', error);
        }
    });

    function updateAudioButton() {
        const icon = audioControl.querySelector('i');
        icon.className = audio.paused ? 'fas fa-play' : 'fas fa-pause';
    }

    // イージングとノイズ関数
    function easeInOutSine(x) {
        return -(Math.cos(Math.PI * x) - 1) / 2;
    }

    function generateNoiseTable() {
        const table = [];
        for (let i = 0; i < 256; i++) {
            table[i] = Math.random() * 2 - 1;
        }
        return table;
    }

    const noiseTable = generateNoiseTable();

    function noise(x, y, z) {
        const X = Math.floor(x) & 255;
        const Y = Math.floor(y) & 255;
        const Z = Math.floor(z) & 255;

        const fx = x - Math.floor(x);
        const fy = y - Math.floor(y);
        const fz = z - Math.floor(z);

        const u = fade(fx);
        const v = fade(fy);
        const w = fade(fz);

        const A = (noiseTable[X] + Y) & 255;
        const B = (noiseTable[X + 1] + Y) & 255;
        const AA = (noiseTable[A] + Z) & 255;
        const AB = (noiseTable[A + 1] + Z) & 255;
        const BA = (noiseTable[B] + Z) & 255;
        const BB = (noiseTable[B + 1] + Z) & 255;

        return lerp(w, lerp(v, lerp(u, grad(noiseTable[AA], fx, fy, fz),
            grad(noiseTable[BA], fx - 1, fy, fz)),
            lerp(u, grad(noiseTable[AB], fx, fy - 1, fz),
                grad(noiseTable[BB], fx - 1, fy - 1, fz))),
            lerp(v, lerp(u, grad(noiseTable[AA + 1], fx, fy, fz - 1),
                grad(noiseTable[BA + 1], fx - 1, fy, fz - 1)),
                lerp(u, grad(noiseTable[AB + 1], fx, fy - 1, fz - 1),
                    grad(noiseTable[BB + 1], fx - 1, fy - 1, fz - 1))));
    }

    function fade(t) {
        return t * t * t * (t * (t * 6 - 15) + 10);
    }

    function lerp(t, a, b) {
        return a + t * (b - a);
    }

    function grad(hash, x, y, z) {
        const h = hash & 15;
        const u = h < 8 ? x : y;
        const v = h < 4 ? y : h === 12 || h === 14 ? x : z;
        return ((h & 1) === 0 ? u : -u) + ((h & 2) === 0 ? v : -v);
    }

    function lerpColor(color1, color2, t) {
        return {
            r: color1.r + (color2.r - color1.r) * t,
            g: color1.g + (color2.g - color1.g) * t,
            b: color1.b + (color2.b - color1.b) * t
        };
    }

    const shapeColors = {
        TORUS: { r: 1.0, g: 1.0, b: 0.0 },
        SPHERE: { r: 1.0, g: 0.5, b: 0.0 },
        LISSAJOUS: { r: 1.0, g: 0.0, b: 0.5 },
        DNA_HELIX: { r: 0.0, g: 1.0, b: 0.2 },
        // FRACTAL_CUBE removed
        GALAXY_SPIRAL: { r: 0.0, g: 0.8, b: 1.0 },
        WAVE_FORM: { r: 1.0, g: 0.2, b: 0.0 },
        SUPERNOVA: { r: 1.0, g: 0.1, b: 0.1 }, // 赤〜オレンジ
        QUANTUM_FIELD: { r: 0.0, g: 1.0, b: 1.0 }, // シアン
        TRAIN_WHEEL: { r: 1.0, g: 0.8, b: 0.0 }, // ゴールド
        RAIL_TRACK: { r: 0.0, g: 0.5, b: 1.0 }, // 青
        SHINING_STAR: { r: 1.0, g: 1.0, b: 0.8 } // 白〜黄色
    };

    // パーティクルシステムの初期化
    function initParticleSystem() {
        console.log('Initializing particle system...');

        torusPositions = generateTorusPositions();
        spherePositions = generateSpherePositions();
        lissajousPositions = generateLissajousPositions();
        dnaHelixPositions = generateDnaHelixPositions();
        fractalCubePositions = generateFractalCubePositions();
        galaxySpiralPositions = generateGalaxySpiralPositions();
        waveFormPositions = generateWaveFormPositions();
        supernovaPositions = generateSupernovaPositions();
        quantumFieldPositions = generateQuantumFieldPositions();
        trainWheelPositions = generateTrainWheelPositions();
        railTrackPositions = generateRailTrackPositions();
        shiningStarPositions = generateShiningStarPositions();

        particleGeometry = new THREE.BufferGeometry();

        particlePositions = new Float32Array(torusPositions);
        particleGeometry.setAttribute('position', new THREE.BufferAttribute(particlePositions, 3));

        particleColors = new Float32Array(PARTICLE_COUNT * 3);
        for (let i = 0; i < PARTICLE_COUNT; i++) {
            particleColors[i * 3] = shapeColors.TORUS.r;
            particleColors[i * 3 + 1] = shapeColors.TORUS.g;
            particleColors[i * 3 + 2] = shapeColors.TORUS.b;
        }
        particleGeometry.setAttribute('color', new THREE.BufferAttribute(particleColors, 3));

        particleMaterial = new THREE.PointsMaterial({
            size: 8.0, // 20.0→8.0に適正化（形状が見やすいサイズ）
            sizeAttenuation: true,
            vertexColors: true,
            blending: THREE.NormalBlending,
            transparent: true,
            opacity: 0.95
        });

        particleSystem = new THREE.Points(particleGeometry, particleMaterial);

        console.log('Particle system initialized successfully.');
        return particleSystem;
    }

    function getNextShape(current) {
        // 歌詞のストーリーに合わせた順序
        // 車輪 -> 線路 -> 星 -> 銀河 -> 超新星 -> 量子場 -> 波形 -> 球体 -> トーラス
        const shapes = ['TRAIN_WHEEL', 'RAIL_TRACK', 'SHINING_STAR', 'GALAXY_SPIRAL', 'SUPERNOVA', 'QUANTUM_FIELD', 'WAVE_FORM', 'SPHERE', 'TORUS'];
        const currentIndex = shapes.indexOf(current);
        return shapes[(currentIndex + 1) % shapes.length];
    }

    function getShapePositions(shapeName) {
        switch (shapeName) {
            case 'TORUS': return torusPositions;
            case 'SPHERE': return spherePositions;
            case 'LISSAJOUS': return lissajousPositions;
            case 'DNA_HELIX': return dnaHelixPositions;
            case 'FRACTAL_CUBE': return fractalCubePositions;
            case 'GALAXY_SPIRAL': return galaxySpiralPositions;
            case 'WAVE_FORM': return waveFormPositions;
            case 'SUPERNOVA': return supernovaPositions;
            case 'QUANTUM_FIELD': return quantumFieldPositions;
            case 'TRAIN_WHEEL': return trainWheelPositions;
            case 'RAIL_TRACK': return railTrackPositions;
            case 'SHINING_STAR': return shiningStarPositions;
            default: return trainWheelPositions;
        }
    }

    function updatePerformanceLevel() {
        frameCount++;
        const currentTime = Date.now();

        if (currentTime - lastFpsTime > 1000) {
            currentFps = frameCount;
            frameCount = 0;
            lastFpsTime = currentTime;

            if (currentFps < 30) {
                performanceLevel = 'low';
            } else if (currentFps < 45) {
                performanceLevel = 'medium';
            } else {
                performanceLevel = 'high';
            }

            // console.log(`FPS: ${currentFps}, Performance Level: ${performanceLevel}`);
        }
    }

    function getPerformanceSettings() {
        switch (performanceLevel) {
            case 'low':
                return {
                    updateFrequency: 33,
                    batchSize: 1000,
                    colorBatchSize: 5000,
                    noiseScale: 0.03
                };
            case 'medium':
                return {
                    updateFrequency: 22,
                    batchSize: 750,
                    colorBatchSize: 3750,
                    noiseScale: 0.04
                };
            case 'high':
            default:
                return {
                    updateFrequency: 16,
                    batchSize: 500,
                    colorBatchSize: 2500,
                    noiseScale: 0.05
                };
        }
    }

    function updateParticleAnimation() {
        if (!particleSystem || !particleGeometry) return;

        const currentTime = Date.now();
        const settings = getPerformanceSettings();

        updatePerformanceLevel();

        if (currentTime - lastUpdateTime < settings.updateFrequency) {
            frameSkipCounter++;
            if (frameSkipCounter < MAX_FRAME_SKIP) {
                return;
            }
        }

        lastUpdateTime = currentTime;
        frameSkipCounter = 0;

        const time = currentTime * 0.001;

        // オーディオレベルのスムージング（これがないと音楽に反応しない！）
        // bassPeakですでに減衰処理をしているので、ここでは少しだけスムージング
        audioLevelSmooth += (currentAudioLevel - audioLevelSmooth) * 0.3;

        // 音楽連動の強化
        // 2乗することで、音量が大きいときだけ急激に反応するようにする（非線形反応）
        // bassPeakを使っているので、すでにパンチがある。係数を調整。
        const audioExplosion = Math.pow(audioLevelSmooth, 2.0) * 1.5; // 3.0 -> 1.5 に低減

        // 回転速度も音楽に合わせて加速
        const dynamicRotationSpeed = rotationSpeed * (1.0 + audioExplosion * 2.0);
        globalRotation.x += dynamicRotationSpeed * 0.7;
        globalRotation.y += dynamicRotationSpeed;
        globalRotation.z += dynamicRotationSpeed * 0.3;

        pulsePhase += 0.08 + audioExplosion * 0.1;
        colorWavePhase += 0.05 + audioExplosion * 0.1;

        particleSystem.rotation.x = globalRotation.x;
        particleSystem.rotation.y = globalRotation.y;
        particleSystem.rotation.z = globalRotation.z;

        // 音楽に連動したパルスサイズ（よりダイナミックに）
        const baseSize = 8.0;
        // audioExplosionを使って爆発的なサイズ変化を作る
        const pulseSize = baseSize + Math.sin(pulsePhase) * 2.0 + (audioExplosion * 15.0); // 25.0 -> 15.0 に低減
        particleMaterial.size = pulseSize;

        // 全体のスケール変化（鼓動）
        const beatScale = 1.0 + (audioExplosion * 0.15); // 0.3 -> 0.15 に低減
        particleSystem.scale.set(beatScale, beatScale, beatScale);

        const cycleTime = (currentTime - animationStartTime) % ANIMATION_CYCLE;

        if (cycleTime < SHAPE_STABLE_TIME) {
            isStable = true;
            morphProgress = 0;
        } else {
            if (isStable) {
                isStable = false;
                currentShape = nextShape;
                nextShape = getNextShape(currentShape);
                console.log(`Starting morphing from ${currentShape} to ${nextShape}`);
            }

            const morphTime = cycleTime - SHAPE_STABLE_TIME;
            morphProgress = Math.min(morphTime / MORPHING_TIME, 1);

            const easedProgress = easeInOutSine(morphProgress);

            const currentPositions = getShapePositions(currentShape);
            const targetPositions = getShapePositions(nextShape);
            const noiseScale = settings.noiseScale;

            const batchSize = settings.batchSize;
            for (let batch = 0; batch < PARTICLE_COUNT; batch += batchSize) {
                const endIndex = Math.min(batch + batchSize, PARTICLE_COUNT);

                for (let i = batch; i < endIndex; i++) {
                    const i3 = i * 3;

                    const lerpedX = currentPositions[i3] + (targetPositions[i3] - currentPositions[i3]) * easedProgress;
                    const lerpedY = currentPositions[i3 + 1] + (targetPositions[i3 + 1] - currentPositions[i3 + 1]) * easedProgress;
                    const lerpedZ = currentPositions[i3 + 2] + (targetPositions[i3 + 2] - currentPositions[i3 + 2]) * easedProgress;

                    const noiseX = noise(lerpedX * 0.1, lerpedY * 0.1, time) * noiseScale;
                    const noiseY = noise(lerpedX * 0.1 + 100, lerpedY * 0.1 + 100, time) * noiseScale;
                    const noiseZ = noise(lerpedX * 0.1 + 200, lerpedY * 0.1 + 200, time) * noiseScale;

                    // ビートによる爆発的拡散（Displacement）
                    // 中心からのベクトルを計算し、音量に応じて外側に押し出す
                    const dist = Math.sqrt(lerpedX * lerpedX + lerpedY * lerpedY + lerpedZ * lerpedZ);
                    const explosionFactor = audioExplosion * 0.2 * (1.0 / (dist + 0.1)); // 0.5 -> 0.2 に低減

                    const explodeX = lerpedX * explosionFactor;
                    const explodeY = lerpedY * explosionFactor;
                    const explodeZ = lerpedZ * explosionFactor;

                    particlePositions[i3] = lerpedX + noiseX + explodeX;
                    particlePositions[i3 + 1] = lerpedY + noiseY + explodeY;
                    particlePositions[i3 + 2] = lerpedZ + noiseZ + explodeZ;
                }

                if (batch + batchSize < PARTICLE_COUNT) {
                    setTimeout(() => { }, 0);
                }
            }

            const currentColor = shapeColors[currentShape];
            const targetColor = shapeColors[nextShape];
            const lerpedColor = lerpColor(currentColor, targetColor, easedProgress);

            const colorBatchSize = settings.colorBatchSize;
            for (let batch = 0; batch < PARTICLE_COUNT; batch += colorBatchSize) {
                const endIndex = Math.min(batch + colorBatchSize, PARTICLE_COUNT);

                for (let i = batch; i < endIndex; i++) {
                    const i3 = i * 3;

                    const waveOffset = Math.sin(colorWavePhase + i * 0.01) * 0.2;
                    const gradientFactor = Math.sin(i * 0.005 + time) * 0.3;

                    // 音楽連動：音量が大きいときは明るく発光させる + 色相シフト
                    // 輝きを控えめに調整 (0.8 -> 0.4)
                    const audioBoost = audioExplosion * 0.4;

                    // 音量が大きいとき、色相を少しずらす（例：赤→紫）
                    const hueShift = audioExplosion * 0.2; // 0.3 -> 0.2 に低減

                    // RGB回転のような簡易的な色相シフト
                    let r = lerpedColor.r;
                    let g = lerpedColor.g;
                    let b = lerpedColor.b;

                    if (hueShift > 0.1) {
                        // 簡易的な色相回転
                        const newR = r * (1 - hueShift) + g * hueShift;
                        const newG = g * (1 - hueShift) + b * hueShift;
                        const newB = b * (1 - hueShift) + r * hueShift;
                        r = newR; g = newG; b = newB;
                    }

                    particleColors[i3] = Math.min(1.0, r + waveOffset + gradientFactor + audioBoost);
                    particleColors[i3 + 1] = Math.min(1.0, g + waveOffset * 0.7 + gradientFactor + audioBoost);
                    particleColors[i3 + 2] = Math.min(1.0, b + waveOffset * 0.5 + gradientFactor + audioBoost);
                }
            }

            particleGeometry.attributes.position.needsUpdate = true;
            particleGeometry.attributes.color.needsUpdate = true;
        }
    }

    AFRAME.registerComponent('particle-animation', {
        init: function () {
            this.particleSystem = initParticleSystem();
            this.el.object3D.add(this.particleSystem);
            animationStartTime = Date.now();
            console.log('Particle animation component initialized.');
        },

        tick: function () {
            updateParticleAnimation();
        }
    });

    // DOMContentLoaded以降に実行されるように、initAudioAnalyserの呼び出しをここに移動
    init();
    async function init() {
        await initAudioAnalyser();
    }
});
