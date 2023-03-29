public class Cartas {

	/**
	 * Método con el que se mostrará gráficamente las cartas que vayan apareciendo
	 * en la mano del jugador y en la del crupier
	 */
	public static void dibujarCarta(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta, String palo) {
		// Dibujar el rectángulo externo e interno de la carta
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 72, 108, Colores.WHITE);
		mesa.dibujarRectangulo(posXdeCarta + 4, posYdeCarta + 5, anchoCarta - 10, alturaCarta - 10, Colores.DARK_GRAY);

		// Dibujar el símbolo de los palos de las cartas
		if (palo.equals("Picas")) {
			// Dibujar el símbolo de Picas
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 14, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 14, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) - 2,
					posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) + 15 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.BLACK);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 16, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					Colores.BLACK);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 2, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					Colores.BLACK);

		} else if (palo.equals("Diamantes")) {
			// Dibujar el símbolo de Diamantes
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 12, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 18,
					posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.RED);

		} else if (palo.equals("Tréboles")) {
			// Dibujar el símbolo de Tréboles
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 12, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 18,
					posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.BLACK);

		} else if (palo.equals("Corazones")) {
			// Dibujar el símbolo de Corazones
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 14, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 14, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) - 2,
					posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) + 15 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.RED);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 16, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					Colores.RED);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 2, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					Colores.RED);
		}
	}

	public static void main(String[] args) {
		// Resolución de la ventana donde se ejecutará el juego de BlackJack
		int alturaCarta = 108;
		int anchoCarta = 72;
		int alturaMesa = 774;
		int anchoMesa = 1278;

		// Panel de la Máquina de Trazados. El color gris crea un fondo agradable
		MaquinaDeTrazados mesa = new MaquinaDeTrazados(anchoMesa, alturaMesa, "OpenJML BlackJack", Colores.GRAY);

		// Semicírculo verde que imita una mesa de BlackJack real con un borde oscuro
		mesa.dibujarOvaloLleno(1, -(anchoMesa / 2), anchoMesa, anchoMesa, Colores.DARK_GRAY);
		mesa.dibujarOvaloLleno(11, -(anchoMesa / 2), anchoMesa - 20, anchoMesa - 20, Colores.GREEN);

		// Cartas del crupier
		dibujarCarta(mesa, (anchoMesa / 2) - 215, 20, alturaCarta, anchoCarta, "Picas");
		dibujarCarta(mesa, (anchoMesa / 2) - 105, 20, alturaCarta, anchoCarta, "Diamantes");
		dibujarCarta(mesa, (anchoMesa / 2) + 5, 20, alturaCarta, anchoCarta, "Tréboles");
		dibujarCarta(mesa, (anchoMesa / 2) + 115, 20, alturaCarta, anchoCarta, "Corazones");

		// Cartas del jugador
		dibujarCarta(mesa, (anchoMesa / 2) - 215, 280, alturaCarta, anchoCarta, "Picas");
		dibujarCarta(mesa, (anchoMesa / 2) - 105, 280, alturaCarta, anchoCarta, "Diamantes");
		dibujarCarta(mesa, (anchoMesa / 2) + 5, 280, alturaCarta, anchoCarta, "Tréboles");
		dibujarCarta(mesa, (anchoMesa / 2) + 115, 280, alturaCarta, anchoCarta, "Corazones");

		mesa.mostrar();
	}
}
