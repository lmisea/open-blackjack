public class Cartas {

	/**
	 * Método con el que se mostrará gráficamente las cartas que vayan apareciendo
	 * en la mano del jugador y en la del crupier
	 */
	public static void dibujarCarta(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta, String palo) {
		// Dibujar la carta y el rectángulo interno de la carta
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 100, 150, Colores.WHITE);
		mesa.dibujarRectangulo(posXdeCarta + 8, posYdeCarta + 10, 82, 130, Colores.DARK_GRAY);

		// Dibujar el símbolo de los palos de las cartas
		if (palo.equals("Picas")) {
			// Dibujar el símbolo de Picas
			int[] xPuntos = new int[] { posXdeCarta + 38, posXdeCarta + 48, posXdeCarta + 58, posXdeCarta + 48 };
			int[] yPuntos = new int[] { 85, 65, 85, 105 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.RED);
		} else if (palo.equals("Diamantes")) {
			// Dibujar el símbolo de Diamantes
			int[] xPuntos = new int[] { posXdeCarta + 38, posXdeCarta + 48, posXdeCarta + 58, posXdeCarta + 48 };
			int[] yPuntos = new int[] { 85, 65, 85, 105 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.RED);
		} else if (palo.equals("Treboles")) {
			// Dibujar el símbolo de Tréboles
			int[] xPuntos = new int[] { posXdeCarta + 38, posXdeCarta + 48, posXdeCarta + 58, posXdeCarta + 48 };
			int[] yPuntos = new int[] { 85, 65, 85, 105 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.RED);
		} else if (palo.equals("Corazones")) {
			// Dibujar el símbolo de Corazones
			int[] xPuntos = new int[] { posXdeCarta + 38, posXdeCarta + 48, posXdeCarta + 58, posXdeCarta + 48 };
			int[] yPuntos = new int[] { 85, 65, 85, 105 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.RED);
		}
	}

	public static void main(String[] args) {
		// Resolución de la ventana donde se ejecutará el juego de BlackJack
		int altura = 768;
		int ancho = 1278;

		// Creación del panel de la Máquina de Trazados
		MaquinaDeTrazados mesa = new MaquinaDeTrazados(ancho, altura, "Mesa de blackjack", Colores.WHITE);

		// Semicírculo verde que imita una mesa de BlackJack real
		mesa.dibujarOvaloLleno(1, -(ancho / 2), ancho, ancho, Colores.GREEN);

		dibujarCarta(mesa, (ancho / 2) - 215, 10, "Picas");
		dibujarCarta(mesa, (ancho / 2) - 105, 10, "Diamantes");
		dibujarCarta(mesa, (ancho / 2) + 5, 10, "Treboles");
		dibujarCarta(mesa, (ancho / 2) + 115, 10, "Corazones");

		mesa.mostrar();
	}
}
