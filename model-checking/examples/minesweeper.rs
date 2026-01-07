use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use model_checking::{CtlChecker, CtlFormula, TransitionSystem, Var};

struct MinesweeperConfig {
    mines: u16,
    neighbor_counts: [u8; 16],
}

impl MinesweeperConfig {
    fn new(mines: u16) -> Self {
        let mut neighbor_counts = [0u8; 16];
        
        for pos in 0..16 {
            let row = pos / 4;
            let col = pos % 4;
            let mut count = 0;
            
            for dr in -1..=1 {
                for dc in -1..=1 {
                    if dr == 0 && dc == 0 {
                        continue;
                    }
                    let nr = row as i32 + dr;
                    let nc = col as i32 + dc;
                    if nr >= 0 && nr < 4 && nc >= 0 && nc < 4 {
                        let neighbor_pos = (nr * 4 + nc) as usize;
                        if (mines & (1 << neighbor_pos)) != 0 {
                            count += 1;
                        }
                    }
                }
            }
            neighbor_counts[pos] = count;
        }
        
        Self { mines, neighbor_counts }
    }

    fn has_mine(&self, pos: usize) -> bool {
        (self.mines & (1 << pos)) != 0
    }

    fn get_neighbor_count(&self, pos: usize) -> u8 {
        self.neighbor_counts[pos]
    }

    fn mine_count(&self) -> u32 {
        self.mines.count_ones()
    }
}

struct MinesweeperModel {
    bdd: Rc<Bdd>,
    ts: TransitionSystem,
    config: MinesweeperConfig,
    /// Переменные для открытых клеток (16 переменных)
    revealed_vars: Vec<(Ref, Ref)>, // (present, next)
    /// Переменная для game_over
    game_over_var: (Ref, Ref),
    /// Переменная для won
    won_var: (Ref, Ref),
}

impl MinesweeperModel {
    fn new(mines: u16) -> Self {
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd.clone());
        let config = MinesweeperConfig::new(mines);

        // Объявляем переменные для каждой клетки (открыта/закрыта)
        let mut revealed_vars = Vec::new();
        for i in 0..16 {
            let var = Var::new(format!("r{}", i));
            ts.declare_var(var.clone());
            
            let present = ts.var_manager().get_present(&var).unwrap();
            let next = ts.var_manager().get_next(&var).unwrap();
            revealed_vars.push((bdd.mk_var(present), bdd.mk_var(next)));
        }

        // Переменная game_over
        let game_over = Var::new("game_over");
        ts.declare_var(game_over.clone());
        let go_present = ts.var_manager().get_present(&game_over).unwrap();
        let go_next = ts.var_manager().get_next(&game_over).unwrap();
        let game_over_var = (bdd.mk_var(go_present), bdd.mk_var(go_next));

        // Переменная won
        let won = Var::new("won");
        ts.declare_var(won.clone());
        let won_present = ts.var_manager().get_present(&won).unwrap();
        let won_next = ts.var_manager().get_next(&won).unwrap();
        let won_var = (bdd.mk_var(won_present), bdd.mk_var(won_next));

        Self {
            bdd,
            ts,
            config,
            revealed_vars,
            game_over_var,
            won_var,
        }
    }

    /// BDD для: клетка i открыта
    fn cell_revealed(&self, cell: usize) -> Ref {
        self.revealed_vars[cell].0
    }

    /// BDD для: клетка i открыта (next state)
    fn cell_revealed_next(&self, cell: usize) -> Ref {
        self.revealed_vars[cell].1
    }

    /// BDD для: клетка i не изменилась
    fn cell_unchanged(&self, cell: usize) -> Ref {
        self.bdd.apply_eq(self.revealed_vars[cell].1, self.revealed_vars[cell].0)
    }

    /// Построить модель игры
    fn build(&mut self) {
        // Начальное состояние: все клетки закрыты, игра не окончена
        let mut initial = self.bdd.one();
        for i in 0..16 {
            initial = self.bdd.apply_and(initial, self.bdd.apply_not(self.cell_revealed(i)));
        }
        initial = self.bdd.apply_and(initial, self.bdd.apply_not(self.game_over_var.0));
        initial = self.bdd.apply_and(initial, self.bdd.apply_not(self.won_var.0));
        self.ts.set_initial(initial);

        let mut all_transitions = self.bdd.zero();

        // Переходы: открыть клетку (если игра не окончена)
        let game_not_over = self.bdd.apply_not(self.game_over_var.0);
        let not_won = self.bdd.apply_not(self.won_var.0);
        let can_move = self.bdd.apply_and(game_not_over, not_won);

        for cell in 0..16 {
            // Условие: клетка закрыта и игра не окончена
            let cell_closed = self.bdd.apply_not(self.cell_revealed(cell));
            let guard = self.bdd.apply_and(can_move, cell_closed);

            if self.config.has_mine(cell) {
                // Открываем мину -> game_over
                let mut effect = self.cell_revealed_next(cell);
                effect = self.bdd.apply_and(effect, self.game_over_var.1);
                effect = self.bdd.apply_and(effect, self.bdd.apply_not(self.won_var.1));

                // Остальные клетки не меняются
                for other in 0..16 {
                    if other != cell {
                        effect = self.bdd.apply_and(effect, self.cell_unchanged(other));
                    }
                }

                let transition = self.bdd.apply_and(guard, effect);
                all_transitions = self.bdd.apply_or(all_transitions, transition);
            } else {
                // Открываем безопасную клетку
                let mut effect = self.cell_revealed_next(cell);

                // Проверяем победу: все безопасные клетки открыты
                let mut all_safe_open = self.bdd.one();
                for pos in 0..16 {
                    if !self.config.has_mine(pos) {
                        if pos == cell {
                            all_safe_open = self.bdd.apply_and(all_safe_open, self.cell_revealed_next(pos));
                        } else {
                            all_safe_open = self.bdd.apply_and(all_safe_open, self.cell_revealed(pos));
                        }
                    }
                }

                // Если все безопасные открыты -> победа
                let won_next = all_safe_open;
                effect = self.bdd.apply_and(effect, self.bdd.apply_eq(self.won_var.1, won_next));
                effect = self.bdd.apply_and(effect, self.bdd.apply_not(self.game_over_var.1));

                // Остальные клетки не меняются
                for other in 0..16 {
                    if other != cell {
                        effect = self.bdd.apply_and(effect, self.cell_unchanged(other));
                    }
                }

                let transition = self.bdd.apply_and(guard, effect);
                all_transitions = self.bdd.apply_or(all_transitions, transition);
            }
        }

        // Терминальные состояния (game_over или won) имеют self-loop
        let terminal = self.bdd.apply_or(self.game_over_var.0, self.won_var.0);
        let mut self_loop = self.bdd.apply_eq(self.game_over_var.1, self.game_over_var.0);
        self_loop = self.bdd.apply_and(self_loop, self.bdd.apply_eq(self.won_var.1, self.won_var.0));
        for i in 0..16 {
            self_loop = self.bdd.apply_and(self_loop, self.cell_unchanged(i));
        }
        let terminal_transition = self.bdd.apply_and(terminal, self_loop);
        all_transitions = self.bdd.apply_or(all_transitions, terminal_transition);

        self.ts.set_transition(all_transitions);

        // Добавляем метки
        self.ts.add_label("game_over".to_string(), self.game_over_var.0);
        self.ts.add_label("won".to_string(), self.won_var.0);
        
        let safe = self.bdd.apply_not(self.game_over_var.0);
        self.ts.add_label("safe".to_string(), safe);
    }

    fn get_ts(&self) -> &TransitionSystem {
        &self.ts
    }

    fn get_bdd(&self) -> &Bdd {
        &self.bdd
    }

    fn get_config(&self) -> &MinesweeperConfig {
        &self.config
    }
}

fn print_board(config: &MinesweeperConfig) {
    println!("\n  Конфигурация поля 4x4:");
    println!("  ┌───┬───┬───┬───┐");
    for row in 0..4 {
        print!("  │");
        for col in 0..4 {
            let pos = row * 4 + col;
            if config.has_mine(pos) {
                print!(" 💣│");
            } else {
                let count = config.get_neighbor_count(pos);
                if count == 0 {
                    print!("   │");
                } else {
                    print!(" {} │", count);
                }
            }
        }
        println!();
        if row < 3 {
            println!("  ├───┼───┼───┼───┤");
        }
    }
    println!("  └───┴───┴───┴───┘");
}

fn analyze_game(mines: u16, scenario_name: &str) {
    println!("\n╔═══════════════════════════════════════════════════════════╗");
    println!("║ {}                                                        ", scenario_name);
    println!("╚═══════════════════════════════════════════════════════════╝");

    let mut model = MinesweeperModel::new(mines);
    print_board(model.get_config());
    
    println!("\n📊 Статистика поля:");
    println!("   • Всего клеток: 16");
    println!("   • Мин: {}", model.get_config().mine_count());
    println!("   • Безопасных клеток: {}", 16 - model.get_config().mine_count());

    println!("\n🔨 Построение модели...");
    model.build();
    
    let ts = model.get_ts();
    let bdd = model.get_bdd();

    println!("   • Переменных состояния: {}", 16 + 2);
    println!("   • Всего BDD переменных: {}", (16 + 2) * 2);

    println!("\n🔍 Анализ пространства состояний...");
    let reachable = ts.reachable();
    
    if let Some(count) = ts.count_states(reachable) {
        println!("   • Достижимых состояний: {}", count);
    }

    println!("\n═══════════════════════════════════════════════════════════");
    println!("  Проверка свойств CTL");
    println!("═══════════════════════════════════════════════════════════\n");

    let ts_rc = Rc::new(ts.clone());
    let checker = CtlChecker::new(ts_rc.clone());

    // Свойство 1: EF won - существует путь к победе
    println!("1️⃣  Свойство: EF won");
    println!("   Существует ли стратегия победы?\n");
    
    let ef_won = CtlFormula::atom("won").ef();
    let can_win = checker.check(&ef_won);
    
    if !bdd.is_zero(can_win) {
        println!("   ✅ ПОБЕДА ВОЗМОЖНА!");
        if let Some(count) = ts.count_states(can_win) {
            println!("   Состояний, из которых можно выиграть: {}", count);
        }
    } else {
        println!("   ❌ ПОБЕДА НЕВОЗМОЖНА!");
        println!("   Model checking доказал, что НЕ СУЩЕСТВУЕТ");
        println!("   последовательности ходов, ведущей к победе!");
    }

    // Свойство 2: EF(won ∧ ¬game_over) - можно выиграть без взрыва
    println!("\n2️⃣  Свойство: EF(won ∧ ¬game_over)");
    println!("   Можно ли выиграть без взрыва?\n");
    
    let won_safely = CtlFormula::atom("won").and(CtlFormula::atom("game_over").not());
    let ef_won_safely = won_safely.ef();
    let can_win_safely = checker.check(&ef_won_safely);
    
    if !bdd.is_zero(can_win_safely) {
        println!("   ✅ МОЖНО ВЫИГРАТЬ БЕЗОПАСНО!");
        if let Some(count) = ts.count_states(can_win_safely) {
            println!("   Безопасных выигрышных состояний: {}", count);
        }
    } else {
        println!("   ❌ Безопасная победа невозможна");
    }

    // Итоговая статистика
    println!("\n═══════════════════════════════════════════════════════════");
    println!("  Итоговая статистика");
    println!("═══════════════════════════════════════════════════════════\n");

    let game_over_states = ts.get_label("game_over").unwrap();
    let won_states = ts.get_label("won").unwrap();
    
    let game_over_reachable = bdd.apply_and(game_over_states, reachable);
    let won_reachable = bdd.apply_and(won_states, reachable);

    if let Some(go_count) = ts.count_states(game_over_reachable) {
        println!("  💥 Состояний с взрывом: {}", go_count);
    }
    
    if let Some(win_count) = ts.count_states(won_reachable) {
        println!("  🎉 Выигрышных состояний: {}", win_count);
    }
}

fn main() {
    println!("╔═══════════════════════════════════════════════════════════╗");
    println!("║   Сапёр 4x4 - Model Checking для игры Minesweeper        ║");
    println!("╚═══════════════════════════════════════════════════════════╝\n");

    println!("Демонстрация двух сценариев:");
    println!("  1. Выигрываемая игра (3 мины)");
    println!("  2. Невыигрываемая игра (14 мин, 2 изолированные клетки)\n");

    // Сценарий 1: Выигрываемая игра с 3 минами
    // Позиции: (0,1), (1,3), (3,2) = биты 1, 7, 14
    let mines_winnable = (1 << 1) | (1 << 7) | (1 << 14);
    analyze_game(mines_winnable, "Сценарий 1: Выигрываемая игра (3 мины)");

    // Сценарий 2: Невыигрываемая игра - 14 мин из 16 клеток
    // Оставляем 2 безопасные клетки: (0,0) и (3,3) = биты 0 и 15
    // Все остальные клетки - мины
    let mines_unwinnable = 0xFFFF & !(1 << 0) & !(1 << 15); // Все кроме битов 0 и 15
    analyze_game(mines_unwinnable, "Сценарий 2: Невыигрываемая (14 мин, 2 клетки)");

}
